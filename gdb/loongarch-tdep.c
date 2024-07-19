/* Target-dependent code for GNU/Linux LoongArch.

   Copyright (C) 2021 Free Software Foundation, Inc.
   Contributed by Loongson Ltd.

   This file is part of GDB.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#include "defs.h"
#include "frame.h"
#include "inferior.h"
#include "symtab.h"
#include "value.h"
#include "gdbcmd.h"
#include "language.h"
#include "gdbcore.h"
#include "symfile.h"
#include "objfiles.h"
#include "gdbtypes.h"
#include "target.h"
#include "arch-utils.h"
#include "regcache.h"
#include "osabi.h"
#include "block.h"
#include "reggroups.h"
#include "elf-bfd.h"
#include "symcat.h"
#include "dis-asm.h"
#include "frame-unwind.h"
#include "frame-base.h"
#include "trad-frame.h"
#include "infcall.h"
#include "floatformat.h"
#include "remote.h"
#include "target-descriptions.h"
#include "dwarf2/frame.h"
#include "user-regs.h"
#include "valprint.h"
#include "gdbsupport/common-defs.h"
#include "cli/cli-decode.h"
#include "observable.h"
#include "loongarch-tdep.h"
#include "arch/loongarch.h"

#include <algorithm>

/* Figure out where the longjmp will land.
   We expect the first arg to be a pointer to the jmp_buf structure
   from which we extract the pc (LOONGARCH_JB_PC) that we will land
   at.  The pc is copied into PC.  This routine returns 1 on
   success.  */
#define LOONGARCH_JB_PC 0

static int
loongarch_rlen (struct gdbarch *gdbarch)
{
  if (EF_LOONGARCH_IS_LP64 (gdbarch_tdep (gdbarch)->ef_abi))
    return 64;
  else if (EF_LOONGARCH_IS_ILP32 (gdbarch_tdep (gdbarch)->ef_abi))
      return 32;
  else
      gdb_assert_not_reached ("unknown ABI");
  return 0;
}

static insn_t
loongarch_fetch_instruction (CORE_ADDR addr, int *errp)
{
  size_t insnlen = loongarch_insn_length (0);
  gdb_byte buf[insnlen];
  int err;
  ULONGEST ret;

  err = target_read_memory (addr, buf, insnlen);
  if (errp != NULL)
    *errp = err;
  if (err != 0)
    {
      if (errp == NULL)
	memory_error (TARGET_XFER_E_IO, addr);
      return 0;
    }
  ret = extract_unsigned_integer (buf, insnlen, BFD_ENDIAN_LITTLE);
  return ret;
}

static int
loongarch_insn_is_branch_and_must_branch (insn_t insn)
{
  if ((insn & 0xfc000000) == 0x4c000000	    /* jirl r0:5,r5:5,s10:16<<2 */
      || (insn & 0xfc000000) == 0x50000000  /* b sb0:10|10:16<<2 */
      || (insn & 0xfc000000) == 0x54000000) /* bl sb0:10|10:16<<2 */
    return 1;
  return 0;
}

static int
loongarch_insn_is_branch (insn_t insn)
{
  if (loongarch_insn_is_branch_and_must_branch (insn)
      || (insn & 0xfc000000) == 0x40000000  /* beqz r5:5,sb0:5|10:16<<2 */
      || (insn & 0xfc000000) == 0x44000000  /* bnez r5:5,sb0:5|10:16<<2 */
      || (insn & 0xfc000300) == 0x48000000  /* bceqz c5:3,sb0:5|10:16<<2 */
      || (insn & 0xfc000300) == 0x48000100  /* bcnez c5:3,sb0:5|10:16<<2 */
      || (insn & 0xfc000000) == 0x58000000  /* beq r5:5,r0:5,sb10:16<<2 */
      || (insn & 0xfc000000) == 0x5c000000  /* bne r5:5,r0:5,sb10:16<<2 */
      || (insn & 0xfc000000) == 0x60000000  /* blt r5:5,r0:5,sb10:16<<2 */
      || (insn & 0xfc000000) == 0x64000000  /* bge r5:5,r0:5,sb10:16<<2 */
      || (insn & 0xfc000000) == 0x68000000  /* bltu r5:5,r0:5,sb10:16<<2 */
      || (insn & 0xfc000000) == 0x6c000000) /* bgeu r5:5,r0:5,sb10:16<<2 */
    return 1;
  return 0;
}

static CORE_ADDR
loongarch_next_pc_if_branch (struct regcache *regcache, CORE_ADDR cur_pc,
			     insn_t insn)
{
  struct gdbarch *gdbarch = regcache->arch ();
  auto regs = &gdbarch_tdep (gdbarch)->regs;
  CORE_ADDR next_pc;

  if ((insn & 0xfc000000) == 0x40000000	    /* beqz r5:5,sb0:5|10:16<<2 */
      || (insn & 0xfc000000) == 0x44000000  /* bnez r5:5,sb0:5|10:16<<2 */
      || (insn & 0xfc000300) == 0x48000000  /* bceqz c5:3,sb0:5|10:16<<2 */
      || (insn & 0xfc000300) == 0x48000100) /* bcnez c5:3,sb0:5|10:16<<2 */
    next_pc = cur_pc + loongarch_decode_imm ("0:5|10:16<<2", insn, 1);
  else if ((insn & 0xfc000000) == 0x4c000000) /* jirl r0:5,r5:5,s10:16<<2 */
    next_pc = regcache_raw_get_signed (
		regcache, regs->r + loongarch_decode_imm ("5:5", insn, 0))
	      + loongarch_decode_imm ("10:16<<2", insn, 1);
  else if ((insn & 0xfc000000) == 0x50000000	 /* b sb0:10|10:16<<2 */
	   || (insn & 0xfc000000) == 0x54000000) /* bl sb0:10|10:16<<2 */
    next_pc = cur_pc + loongarch_decode_imm ("0:10|10:16<<2", insn, 1);
  else if ((insn & 0xfc000000) == 0x58000000	/* beq r5:5,r0:5,sb10:16<<2 */
	   || (insn & 0xfc000000) == 0x5c000000 /* bne r5:5,r0:5,sb10:16<<2 */
	   || (insn & 0xfc000000) == 0x60000000 /* blt r5:5,r0:5,sb10:16<<2 */
	   || (insn & 0xfc000000) == 0x64000000 /* bge r5:5,r0:5,sb10:16<<2 */
	   || (insn & 0xfc000000) == 0x68000000 /* bltu r5:5,r0:5,sb10:16<<2 */
	   || (insn & 0xfc000000)
		== 0x6c000000) /* bgeu r5:5,r0:5,sb10:16<<2 */
    next_pc = cur_pc + loongarch_decode_imm ("10:16<<2", insn, 1);
  else
    gdb_assert_not_reached ("I don't know what branch is this");

  return next_pc;
}

/* Checks for an atomic sequence of instructions beginning with a LL/LLD
   instruction and ending with a SC/SCD instruction.  If such a sequence
   is found, attempt to step through it.  A breakpoint is placed at the end of
   the sequence.  */

static std::vector<CORE_ADDR>
loongarch_deal_with_atomic_sequence (struct regcache *regcache, CORE_ADDR pc)
{
  struct gdbarch *gdbarch = regcache->arch ();
  CORE_ADDR next_pc;
  std::vector<CORE_ADDR> next_pcs;
  insn_t insn = loongarch_fetch_instruction (pc, NULL);
  size_t insnlen = loongarch_insn_length (insn);
  int i, atomic_sequence_length, found_atomic_sequence_endpoint;

  if ((insn & 0xff000000) != 0x20000000	    /* ll.w */
      && (insn & 0xff000000) != 0x22000000) /* ll.d */
    return {};

  if (loongarch_debug)
    fprintf_unfiltered (gdb_stdlog,
			"Single step: PC: %s OK, I found ll\\.[wd] here. It's "
			"atomic sequence?\n",
			paddress (gdbarch, pc));

  atomic_sequence_length = 30; /* Magic.  */
  found_atomic_sequence_endpoint = 0;
  for (pc += insnlen, i = 0; i < atomic_sequence_length; pc += insnlen, i++)
    {
      insn = loongarch_fetch_instruction (pc, NULL);
      insnlen = loongarch_insn_length (insn);

      if (loongarch_insn_is_branch_and_must_branch (insn))
	{
	  if (loongarch_debug)
	    fprintf_unfiltered (
	      gdb_stdlog,
	      "Single step: PC: %s Must branch here. Treat it normally.\n",
	      paddress (gdbarch, pc));
	  break;
	}
      else if (loongarch_insn_is_branch (insn))
	{
	  next_pc = loongarch_next_pc_if_branch (regcache, pc, insn);

	  if (loongarch_debug)
	    fprintf_unfiltered (gdb_stdlog,
				"Single step: PC: %s May branch inside and "
				"target is %s. Breakpoint there.\n",
				paddress (gdbarch, pc),
				paddress (gdbarch, next_pc));

	  next_pcs.push_back (next_pc);
	}
      else if ((insn & 0xff000000) == 0x21000000     /* sc.w */
	       || (insn & 0xff000000) == 0x23000000) /* sc.d */
	{
	  found_atomic_sequence_endpoint = 1;
	  next_pc = pc + insnlen;

	  if (loongarch_debug)
	    fprintf_unfiltered (gdb_stdlog,
				"Single step: PC: %s I found sc\\.[wd] and "
				"atomic sequence ends at here.\n"
				"Breakpoint next pc: %s.\n",
				paddress (gdbarch, pc),
				paddress (gdbarch, next_pc));

	  next_pcs.push_back (next_pc);
	  break;
	}
    }

  if (!found_atomic_sequence_endpoint)
    {
      if (loongarch_debug)
	fprintf_unfiltered (
	  gdb_stdlog,
	  "Single step: PC: %s Not ends with sc\\.[wd] in %d insns?\n"
	  "Treat it as not atomic sequence.\n",
	  paddress (gdbarch, pc), atomic_sequence_length);

      return {};
    }

  return next_pcs;
}

/* Implement LoongArch software single step.  */

std::vector<CORE_ADDR>
loongarch_software_single_step (struct regcache *regcache);
std::vector<CORE_ADDR>
loongarch_software_single_step (struct regcache *regcache)
{
  struct gdbarch *gdbarch = regcache->arch ();
  struct gdbarch_tdep *tdep = gdbarch_tdep (gdbarch);
  CORE_ADDR pc = regcache_read_pc (regcache);
  std::vector<CORE_ADDR> next_pcs
    = loongarch_deal_with_atomic_sequence (regcache, pc);

  if (!next_pcs.empty ())
    return next_pcs;

  insn_t insn = loongarch_fetch_instruction (pc, NULL);
  size_t insnlen = loongarch_insn_length (insn);
  CORE_ADDR next = pc + insnlen;

  if ((insn & 0xffff8000) == 0x002b0000 && tdep->syscall_next_pc)
    {
      CORE_ADDR syscall_next = tdep->syscall_next_pc (get_current_frame ());
      if (syscall_next != -1)
	{
	  if (loongarch_debug)
	    fprintf_unfiltered (gdb_stdlog,
				"PC: %s Syscall found. Next pc is %s.\n",
				paddress (gdbarch, pc),
				paddress (gdbarch, syscall_next));
	  return {syscall_next};
	}
    }

  if (loongarch_insn_is_branch (insn))
    {
      CORE_ADDR branch_tgt = loongarch_next_pc_if_branch (regcache, pc, insn);
      if (loongarch_debug)
	fprintf_unfiltered (
	  gdb_stdlog, "PC: %s Next pc is %s if branch, %s for non-branch.\n",
	  paddress (gdbarch, pc), paddress (gdbarch, branch_tgt),
	  paddress (gdbarch, next));
      return {next, branch_tgt};
    }
  else
    {
      if (loongarch_debug)
	fprintf_unfiltered (gdb_stdlog, "PC: %s Next pc is %s.\n",
			    paddress (gdbarch, pc), paddress (gdbarch, next));
      return {next};
    }
}

/* Callback function for user_reg_add.  */

static struct value *
value_of_loongarch_user_reg (struct frame_info *frame, const void *baton)
{
  return value_of_register ((long long) baton, frame);
}

/* Implement the register_name gdbarch method.  */

static const char *
loongarch_register_name (struct gdbarch *gdbarch, int regnum)
{
  auto regs = &gdbarch_tdep (gdbarch)->regs;

  if ((0 <= regs->r && regs->r <= regnum && regnum < regs->r + 32)
    && (EF_LOONGARCH_IS_LP64 (gdbarch_tdep (gdbarch)->ef_abi)))
	return loongarch_r_lp64_name[regnum - regs->r] + 1;

  else if ((0 <= regs->f && regs->f <= regnum && regnum < regs->f + 32)
    && (EF_LOONGARCH_IS_LP64 (gdbarch_tdep (gdbarch)->ef_abi)))
	return loongarch_f_lp64_name[regnum - regs->f] + 1;

  return tdesc_register_name (gdbarch, regnum);
}

/* Analyze the function prologue from START_PC to LIMIT_PC.  Builds
   the associated FRAME_CACHE if not null.
   Return the address of the first instruction past the prologue.  */

static CORE_ADDR
loongarch_scan_prologue (struct gdbarch *gdbarch, CORE_ADDR start_pc,
			 CORE_ADDR limit_pc, struct frame_info *this_frame,
			 struct trad_frame_cache *this_cache)
{
  auto regs = &gdbarch_tdep (gdbarch)->regs;
  int rlen_is_64b = (loongarch_rlen (gdbarch) == 64);

  CORE_ADDR cur_pc, prologue_end = 0;
  insn_t insn;
  size_t insnlen;

  int sp = regs->sp - regs->r;

  long frame_offset = 0;
  int non_prologue_insns = 0;
  int cfa_unknown = 0;

  /* Try to trace li.  */
  int64_t r_value[32] = {0};
  int r_value_known[32] = {1, 0};

  long r_cfa_offset[32] = {0};
  int r_cfa_offset_p[32] = {0};

  long f_cfa_offset[32] = {0};
  int f_cfa_offset_p[32] = {0};

  if (start_pc + 80 < limit_pc)
    limit_pc = start_pc + 80;

  for (cur_pc = start_pc; cur_pc < limit_pc; cur_pc += insnlen)
    {
      int rd, rj, rk;
      int64_t si12, si20, si14;

      insn = loongarch_fetch_instruction (cur_pc, NULL);
      insnlen = loongarch_insn_length (insn);

      rd = loongarch_decode_imm ("0:5", insn, 0);
      rj = loongarch_decode_imm ("5:5", insn, 0);
      rk = loongarch_decode_imm ("10:5", insn, 0);
      si12 = loongarch_decode_imm ("10:12", insn, 1);
      si20 = loongarch_decode_imm ("5:20", insn, 1);
      si14 = loongarch_decode_imm ("10:14<<2", insn, 1);

      if ((((insn & 0xffc00000) == 0x02800000 /* addi.w sp,sp,si12 */
	    && !rlen_is_64b)
	   || ((insn & 0xffc00000) == 0x02c00000 /* addi.d sp,sp,si12 */
	       && rlen_is_64b))
	  && rd == sp && rj == sp)
	{
	  if (si12 < 0)
	    frame_offset -= si12;
	  else
	    /* Exit loop if a positive stack adjustment is found, which
	       usually means that the stack cleanup code in the function
	       epilogue is reached.  */
	    break;
	  prologue_end = cur_pc + insnlen;
	}
      else if ((((insn & 0xffc00000) == 0x29800000 /* st.w rd,sp,si12 */
		 && !rlen_is_64b)
		|| ((insn & 0xffc00000) == 0x29c00000 /* st.d rd,sp,si12 */
		    && rlen_is_64b))
	       && rj == sp)
	{
	  if (!r_cfa_offset_p[rd] && !r_value_known[rd])
	    r_cfa_offset[rd] = si12 - frame_offset, r_cfa_offset_p[rd] = 1;
	  prologue_end = cur_pc + insnlen;
	}
      else if ((((insn & 0xff000000) == 0x25000000 /* stptr.w rd,sp,si14 */
		 && !rlen_is_64b)
		|| ((insn & 0xff000000) == 0x27000000 /* stptr.d rd,sp,si14 */
		    && rlen_is_64b))
	       && rj == sp)
	{
	  if (!r_cfa_offset_p[rd] && !r_value_known[rd])
	    r_cfa_offset[rd] = si14 - frame_offset, r_cfa_offset_p[rd] = 1;
	  prologue_end = cur_pc + insnlen;
	}
      else if (((insn & 0xffc00000) == 0x2b400000     /* fst.s fd,sp,si12 */
		|| (insn & 0xffc00000) == 0x2bc00000) /* fst.d fd,sp,si12 */
	       && rj == sp)
	{
	  if (!f_cfa_offset_p[rd])
	    f_cfa_offset[rd] = si12 - frame_offset, f_cfa_offset_p[rd] = 1;
	}
      else if ((((insn & 0xffff8000) == 0x00110000 /* sub.w sp,sp,rk */
		 && !rlen_is_64b)
		|| ((insn & 0xffff8000) == 0x00118000 /* sub.d sp,sp,rk */
		    && rlen_is_64b))
	       && rd == sp && rj == sp)
	{
	  if (r_value_known[rk])
	    {
	      frame_offset += r_value[rk];
	      prologue_end = cur_pc + insnlen;
	    }
	  else
	    cfa_unknown = 1;
	}
      else if ((((insn & 0xffff8000) == 0x00100000 /* add.w sp,sp,rk */
		 && !rlen_is_64b)
		|| ((insn & 0xffff8000) == 0x00108000 /* add.d sp,sp,rk */
		    && rlen_is_64b))
	       && rd == sp && rj == sp)
	{
	  if (r_value_known[rk] && r_value[rk] < 0)
	    {
	      frame_offset -= r_value[rk];
	      prologue_end = cur_pc + insnlen;
	    }
	  else
	    cfa_unknown = 1;
	}
      else if ((insn & 0xffff8000) == 0x00150000 /* or rd,sp,$r0 */
	       && rj == sp && rk == 0)
	{
	  sp = rd;
	  prologue_end = cur_pc + insnlen;
	}
      else if ((insn & 0xffc00000) == 0x02800000) /* addi.w rd,rj,si12 */
	{
	  if (r_value_known[rj] && rd != 0)
	    r_value[rd] = (int32_t) (r_value[rj] + si12),
	    r_value_known[rd] = 1;
	}
      else if ((insn & 0xffc00000) == 0x03800000) /* ori rd,rj,si12 */
	{
	  if (r_value_known[rj] && rd != 0)
	    r_value[rd] = r_value[rj] | (si12 & 0xfff), r_value_known[rd] = 1;
	}
      else if ((insn & 0xfe000000) == 0x14000000) /* lu12i.w rd,si20 */
	{
	  if (rd != 0)
	    r_value[rd] = si20 << 12, r_value_known[rd] = 1;
	}
      else if ((insn & 0xfe000000) == 0x16000000) /* lu32i.d rd,si20 */
	{
	  if (r_value_known[rd] && rd != 0)
	    r_value[rd] = (r_value[rd] & 0xffffffff) | (si20 << 32),
	    r_value_known[rd] = 1;
	}
      else if ((insn & 0xffc00000) == 0x03000000) /* lu52i.d rd,rj,si12 */
	{
	  if (r_value_known[rj] && rd != 0)
	    r_value[rd] = (r_value[rj] & 0xfffffffffffff) | (si12 << 52),
	    r_value_known[rd] = 1;
	}
      else if (loongarch_insn_is_branch (insn))
	break; /* Shrink-wrap or end of prologue in a basic block.  */
      else
	non_prologue_insns++;

      /* 4 INSNs for 'la' and one for some other.  */
      if (5 < non_prologue_insns)
	break;
    }

  if (loongarch_debug)
    {
      const char *fun_name;
      find_pc_partial_function (start_pc, &fun_name, NULL, NULL);
      fprintf_unfiltered (gdb_stdlog,
			  "Prologue Analyze: -- Start -- Callee [%s] %s\n",
			  fun_name ? fun_name : "<unknown>",
			  paddress (gdbarch, start_pc));
    }

  do
    {
      int i;
      CORE_ADDR cfa = -1;

      if (!(this_frame && this_cache))
	break;

      if (!cfa_unknown)
	{
	  try
	    {
	      cfa = get_frame_register_signed (this_frame, regs->r + sp)
		    + frame_offset;
	    }
	  catch (const gdb_exception_error &ex)
	    {
	      cfa_unknown = 1;
	      if (ex.error != NOT_AVAILABLE_ERROR)
		throw;
	    }

	  if (loongarch_debug)
	    fprintf_unfiltered (
	      gdb_stdlog,
	      "Prologue Analyze: CFA is (frame pointer $%s + 0x%lx) = %s\n",
	      gdbarch_register_name (gdbarch, regs->r + sp),
	      (long) frame_offset,
	      cfa_unknown ? "<unknown>" : paddress (gdbarch, cfa));
	}
      else if (loongarch_debug)
	fprintf_unfiltered (gdb_stdlog,
			    "Prologue Analyze: Unknown stack frame size, so "
			    "can't get known CFA\n");

      if (r_cfa_offset_p[1] && !cfa_unknown)
	{
	  CORE_ADDR ret_saved = cfa + r_cfa_offset[1];
	  trad_frame_set_reg_addr (this_cache, gdbarch_pc_regnum (gdbarch),
				   ret_saved);
	  if (loongarch_debug)
	    fprintf_unfiltered (
	      gdb_stdlog,
	      "Prologue Analyze: Return addr saved in (CFA - 0x%lx) = %s\n",
	      -r_cfa_offset[1], paddress (gdbarch, ret_saved));
	}
      else if (r_cfa_offset_p[1] /* && cfa_unknown */)
	{
	  if (loongarch_debug)
	    fprintf_unfiltered (gdb_stdlog,
				"Prologue Analyze: Return addr saved in (CFA "
				"- 0x%lx), but CFA is unknown\n",
				-r_cfa_offset[1]);
	}
      else
	{
	  trad_frame_set_reg_realreg (this_cache, gdbarch_pc_regnum (gdbarch),
				      regs->r + 1);
	  if (loongarch_debug)
	    fprintf_unfiltered (gdb_stdlog,
				"Prologue Analyze: No found $r1 pushed in "
				"stack. Return addr saved in $r1\n");
	}

      if (cfa_unknown)
	{
	  trad_frame_set_this_base (this_cache, -1);
	  break;
	}

      trad_frame_set_reg_value (this_cache, gdbarch_sp_regnum (gdbarch),
				(LONGEST) cfa);
      trad_frame_set_this_base (this_cache, cfa);

      if (loongarch_debug)
	fprintf_unfiltered (
	  gdb_stdlog,
	  "Prologue Analyze: Where caller's registers saved as follow:\n");

      for (i = 0; i < 32; i++)
	if (r_cfa_offset_p[i] && i != 1)
	  {
	    trad_frame_set_reg_addr (this_cache, regs->r + i,
				     cfa + r_cfa_offset[i]);
	    if (loongarch_debug)
	      fprintf_unfiltered (
		gdb_stdlog,
		"Prologue Analyze: $%s: saved in (CFA - 0x%lx) = %s\n",
		gdbarch_register_name (gdbarch, regs->r + i), -r_cfa_offset[i],
		paddress (gdbarch, cfa + r_cfa_offset[i]));
	  }

      if (regs->f <= 0)
	for (i = 0; i < 32; i++)
	  {
	    if (f_cfa_offset_p[i])
	      trad_frame_set_reg_addr (this_cache, regs->f + i,
				       cfa + f_cfa_offset[i]);
	    if (loongarch_debug)
	      fprintf_unfiltered (
		gdb_stdlog,
		"Prologue Analyze: $%s: saved in (CFA - 0x%lx) = %s\n",
		gdbarch_register_name (gdbarch, regs->f + i), -f_cfa_offset[i],
		paddress (gdbarch, cfa + f_cfa_offset[i]));
	  }
    }
  while (0);

  if (loongarch_debug)
    fprintf_unfiltered (gdb_stdlog, "Prologue Analyze: -- End -- %s\n",
			paddress (gdbarch, cur_pc));

  return prologue_end ? prologue_end : cur_pc;
}

/* Implement the loongarch_skip_prologue gdbarch method.  */

/* To skip prologues, I use this predicate.  Returns either PC itself
   if the code at PC does not look like a function prologue; otherwise
   returns an address that (if we're lucky) follows the prologue.  If
   LENIENT, then we must skip everything which is involved in setting
   up the frame (it's OK to skip more, just so long as we don't skip
   anything which might clobber the registers which are being saved.
   We must skip more in the case where part of the prologue is in the
   delay slot of a non-prologue instruction).  */

static CORE_ADDR
loongarch_skip_prologue (struct gdbarch *gdbarch, CORE_ADDR pc)
{
  CORE_ADDR limit_pc;
  CORE_ADDR func_addr;

  /* See if we can determine the end of the prologue via the symbol table.
     If so, then return either PC, or the PC after the prologue, whichever
     is greater.  */
  if (find_pc_partial_function (pc, NULL, &func_addr, NULL))
    {
      CORE_ADDR post_prologue_pc
	= skip_prologue_using_sal (gdbarch, func_addr);
      if (post_prologue_pc != 0)
	return std::max (pc, post_prologue_pc);
    }

  /* Can't determine prologue from the symbol table, need to examine
     instructions.  */

  /* Find an upper limit on the function prologue using the debug
     information.  If the debug information could not be used to provide
     that bound, then use an arbitrary large number as the upper bound.  */
  limit_pc = skip_prologue_using_sal (gdbarch, pc);
  if (limit_pc == 0)
    limit_pc = pc + 100; /* Magic.  */

  return loongarch_scan_prologue (gdbarch, pc, limit_pc, NULL, NULL);
}

/* Adjust the address downward (direction of stack growth) so that it
   is correctly aligned for a new stack frame.  */
static CORE_ADDR
loongarch_frame_align (struct gdbarch *gdbarch, CORE_ADDR addr)
{
  return align_down (addr, 16);
}

/* Implement the unwind_pc gdbarch method.  */

static CORE_ADDR
loongarch_unwind_pc (struct gdbarch *gdbarch, struct frame_info *next_frame)
{
  return frame_unwind_register_signed (next_frame,
				       gdbarch_pc_regnum (gdbarch));
}

/* Implement the unwind_sp gdbarch method.  */

static CORE_ADDR
loongarch_unwind_sp (struct gdbarch *gdbarch, struct frame_info *next_frame)
{
  return frame_unwind_register_signed (next_frame,
				       gdbarch_sp_regnum (gdbarch));
}

/* Implement the dummy_id gdbarch method.  */

static struct frame_id
loongarch_dummy_id (struct gdbarch *gdbarch, struct frame_info *this_frame)
{
  return frame_id_build (
    get_frame_register_signed (this_frame, gdbarch_sp_regnum (gdbarch)),
    get_frame_pc (this_frame));
}

/* Generate, or return the cached frame cache for the loongarch frame
   unwinder.  */

static struct trad_frame_cache *
loongarch_frame_cache (struct frame_info *this_frame, void **this_cache)
{
  struct gdbarch *gdbarch = get_frame_arch (this_frame);
  struct trad_frame_cache *cache;
  CORE_ADDR pc, start_addr, stack_addr;

  if (*this_cache != NULL)
    return (struct trad_frame_cache *) *this_cache;
  cache = trad_frame_cache_zalloc (this_frame);
  *this_cache = cache;

  pc = get_frame_address_in_block (this_frame);
  if (find_pc_partial_function (pc, NULL, &start_addr, NULL))
    {
      loongarch_scan_prologue (gdbarch, start_addr, pc, this_frame, cache);
      stack_addr = trad_frame_get_this_base (cache);
      trad_frame_set_id (cache,
			 stack_addr == -1
			   ? frame_id_build_unavailable_stack (start_addr)
			   : frame_id_build (stack_addr, start_addr));
    }
  else
    {
      auto regs = &gdbarch_tdep (gdbarch)->regs;
      trad_frame_set_reg_realreg (cache, regs->ra, -2 /* TF_REG_UNKNOWN */);
      trad_frame_set_reg_realreg (cache, gdbarch_pc_regnum (gdbarch),
				  regs->ra);

      trad_frame_set_id (cache, frame_id_build_unavailable_stack (pc));
    }
  return cache;
}

/* Implement the this_id callback for loongarch frame unwinder.  */

static void
loongarch_frame_this_id (struct frame_info *this_frame, void **prologue_cache,
			 struct frame_id *this_id)
{
  struct trad_frame_cache *info;

  info = loongarch_frame_cache (this_frame, prologue_cache);
  trad_frame_get_id (info, this_id);
}

/* Implement the prev_register callback for loongarch frame unwinder.  */

static struct value *
loongarch_frame_prev_register (struct frame_info *this_frame,
			       void **prologue_cache, int regnum)
{
  struct trad_frame_cache *info;

  info = loongarch_frame_cache (this_frame, prologue_cache);
  return trad_frame_get_register (info, this_frame, regnum);
}

static const struct frame_unwind loongarch_frame_unwind = {
  /*.type	  =*/NORMAL_FRAME,
  /*.stop_reason   =*/default_frame_unwind_stop_reason,
  /*.this_id       =*/loongarch_frame_this_id,
  /*.prev_register =*/loongarch_frame_prev_register,
  /*.unwind_data   =*/NULL,
  /*.sniffer       =*/default_frame_sniffer,
};

typedef struct stack_data_t
{
  const gdb_byte *addr = NULL;
  int len = 0;
  bool ref = false;
} stack_data_t;

static void
pass_on_stack (std::vector<stack_data_t> &stack, const gdb_byte *val, int len,
	       int align, bool ref = false)
{
  stack_data_t buf;
  buf.addr = val;
  buf.len = align_up (len, align);
  buf.ref = ref;

  stack.push_back (buf);
}

static void
pass_on_reg (struct regcache *regcache, int regno, const gdb_byte *val,
	     int len)
{
  gdb_byte reg[32];
  memset (reg, 0, sizeof (reg));
  memcpy (reg, val, len);
  regcache->cooked_write (regno, reg);
}

static void
compute_type_num(struct type *tp, int &complex_num, int &float_num,
                 int &other_num, int &counter, int &float_seq,
                 int &other_seq)
{
  if (tp->code () == TYPE_CODE_COMPLEX)
    complex_num++;
  else if (tp->code () == TYPE_CODE_FLT)
    float_num++;
  else if (tp->code () != TYPE_CODE_STRUCT)
    other_num++;

  /* When the function parameter or return value type is a structure,
     traverse each member in the structure and make relevant marks.  */
  for (int i = 0; i < tp->num_fields (); i++)
    {
      field fd = tp->field (i);
      struct type *t = fd.type ();

      /* Call check_typedef(TYPE_TARGET_TYPE (TYPE)) on our type to make
         sure that, if TYPE is a TYPE_CODE_TYPEDEF, its TYPE is set to
         the target type instead of TYPE_CODE_TYPEDEF.  */
      if (t->code () == TYPE_CODE_TYPEDEF)
        t = check_typedef (TYPE_TARGET_TYPE (t));

      switch (t->code ())
        {
        case TYPE_CODE_STRUCT:
          compute_type_num(t, complex_num, float_num, other_num,
                           counter, float_seq, other_seq);
          break;
        case TYPE_CODE_COMPLEX:
          complex_num++;
          break;
        case TYPE_CODE_FLT:
          float_num++;
          float_seq = ++counter;
          break;
        default:
          other_num++;
          other_seq = ++counter;
          break;
        }
    }
}

static void
pass_small_struct_on_reg (struct gdbarch *gdbarch, struct type *tp,
                          const gdb_byte *data, std::vector<stack_data_t> &gp,
                          std::vector<stack_data_t> &fp)
{
  const int rlen = loongarch_rlen (gdbarch) / 8;
  int len = TYPE_LENGTH (tp);
  int complex_num = 0, float_num = 0, other_num = 0;
  int counter = 0, float_seq = 0, other_seq = 0;
  stack_data_t elm;

  gdb_assert (len <= 2 * rlen);

  /* Compute the relevant members and types in the function parameters
     and mark them.  */
  compute_type_num(tp, complex_num, float_num, other_num,
                   counter, float_seq, other_seq);

  if (other_num > 0 && float_num == 0 && len <= rlen)
    {
      /* For the small structure has only other types (like char/short/int/long
         etc.), and the size does not exceed rlen, pass on one gp or stack.  */
      elm.addr = data;
      elm.len = rlen;
      gp.push_back (elm);
    }
  else if (float_num == 1 && complex_num == 0 && other_num == 0 && len <= rlen)
    {
      /* For the small structure has only floating-point (like float/double),
         and the size does not exceed rlen, pass on one fp or stack.  */
      elm.addr = data;
      elm.len = rlen;
      fp.push_back (elm);
    }
  else if (float_num == 1 && other_num == 1)
    {
      /* For the small structure has only one floating-point type and
         one other type(like float and int, char and double etc.), the
         floating-point type passes through one fp or stack, and the
         other types pass on one gp or stack.  */
      if (float_seq < other_seq)
        {
          /* Floating point first, first pass on fp, then gp.  */
          elm.addr = data;
          if (len == rlen)
            elm.len = rlen / 2;
          else
            elm.len = rlen;
          fp.push_back (elm);
          elm.addr += elm.len;
          gp.push_back (elm);
        }
      else
        {
          /* Floating point after, first pass on gp, then fp.  */
          elm.addr = data;
          if (len == rlen)
            elm.len = rlen / 2;
          else
            elm.len = rlen;
          gp.push_back (elm);
          elm.addr += elm.len;
          fp.push_back (elm);
        }
    }
  else if ((complex_num == 1 && float_num == 0 && other_num == 0) ||
          (float_num ==2 && other_num == 0))
    {
      /* For the small structure has only two floating-point types or
       * one complex number type, pass on two fp or stack.  */
      elm.addr = data;
      /* 2 float or 1 'float _Complex'. */
      if (len == rlen)
        elm.len = rlen / 2;
      /*  2 double or 1 'double _Complex'.  */
      else
        elm.len = rlen;
      fp.push_back (elm);
      elm.addr += elm.len;
      fp.push_back (elm);
    }
  else
    {
      /* For other cases, pass on two gp or stack.  */
            /* For example, the small structure is of the following type,
               1. with more than 2 other types and the size is greater than rlen
            (like struct{int; int; int;}; struct{long; int; short; char;}; etc.).
         2. with 'long double' on fpu64 or 'double' on fpu32
            (like struct{long double;}; or struct{double;}; etc.).
         3. with more than 2 floating-point types
            (like struct{float; float; float;}; struct{float; float; double;};
             struct{float; float; float; float;}; etc.)
         4. with 2 'float _Complex'
            (like struct{float _Complex; float _Complex;} etc.).  */
      elm.addr = data;
      elm.len = rlen;
      gp.push_back (elm);
      elm.addr += elm.len;
      gp.push_back (elm);
    }
}

static bool
try_pass_small_struct_on_reg (struct gdbarch *gdbarch,
			      struct regcache *regcache, struct value *arg,
			      int &gp, int &fp, int gp_max, int fp_max)
{
  const int rlen = loongarch_rlen (gdbarch) / 8;
  struct type *a_type = check_typedef (value_type (arg));
  int len = TYPE_LENGTH (a_type);
  const gdb_byte *val = value_contents (arg);

  std::vector<stack_data_t> gpreg;
  std::vector<stack_data_t> fpreg;

  gdb_assert (len <= 2 * rlen);
  // gdb_assert (a_type->code () == TYPE_CODE_STRUCT);

  pass_small_struct_on_reg (gdbarch, a_type, val, gpreg, fpreg);

  if (gp + gpreg.size () - 1 < gp_max && fp + fpreg.size () - 1 < fp_max)
    {
      for (auto it : gpreg)
	{
	  pass_on_reg (regcache, gp, it.addr, it.len);
	  gp++;
	}
      for (auto it : fpreg)
	{
	  pass_on_reg (regcache, fp, it.addr, it.len);
	  fp++;
	}
      return true;
    }
  return false;
}

/* Implement the push dummy call gdbarch callback.  */

static CORE_ADDR
loongarch_lp32lp64_push_dummy_call (
  struct gdbarch *gdbarch, struct value *function, struct regcache *regcache,
  CORE_ADDR bp_addr, int nargs, struct value **args, CORE_ADDR sp,
  function_call_return_method return_method, CORE_ADDR struct_addr)
{
  const int rlen = loongarch_rlen (gdbarch) / 8;
  auto regs = &gdbarch_tdep (gdbarch)->regs;
  int gp = regs->r + 4;	     /* $a0 = $r4 = regs->r + 4 */
  int fp = regs->f;	     /* $fa0 */
  const int gp_max = gp + 8; /* gpr $a0 ~ $a7 ($r4 ~ $r11) */
  const int fp_max = fp + 8; /* fpr $fa0 ~ $fa7 */
  std::vector<stack_data_t> stack;
  int vec_insn = 0;

  {
    if (return_method != return_method_normal)
      {
	regcache_cooked_write_unsigned (regcache, gp++, struct_addr);
      }

    if (return_method == return_method_hidden_param)
      {
	args++;
	nargs--;
      }
  }
  regcache_cooked_write_signed (regcache, regs->ra, bp_addr);

  struct type *f_type = check_typedef (value_type (function));

  for (int i = 0; i < nargs; i++)
    {
      struct value *arg = args[i];
      struct type *a_type = check_typedef (value_type (arg));
      int len = TYPE_LENGTH (a_type);
      const gdb_byte *val = value_contents (arg);

      switch (a_type->code ())
	{
	case TYPE_CODE_INT:
	case TYPE_CODE_BOOL:
	case TYPE_CODE_CHAR:
	case TYPE_CODE_RANGE:
	case TYPE_CODE_ENUM:
	case TYPE_CODE_PTR:
	  if (gp < gp_max)
	    {
	      if (TYPE_UNSIGNED (a_type))
		{
		  ULONGEST data
		    = extract_unsigned_integer (val, len, BFD_ENDIAN_LITTLE);
		  regcache_cooked_write_unsigned (regcache, gp++, data);
		}
	      else
		{
		  LONGEST data
		    = extract_signed_integer (val, len, BFD_ENDIAN_LITTLE);
		  regcache_cooked_write_signed (regcache, gp++, data);
		}
	    }
	  else
	    {
	      pass_on_stack (stack, val, len, rlen);
	    }
	  break;
	case TYPE_CODE_FLT:
	  if (len <= rlen)
	    {
	      if (!TYPE_VARARGS (f_type) && (fp < fp_max))
		pass_on_reg (regcache, fp++, val, len);
	      else if (gp < gp_max)
		pass_on_reg (regcache, gp++, val, len);
	      else
		pass_on_stack (stack, val, len, rlen);
	    }
	  /* Long double like struct.  */
	  else
	    {
	      if (gp < gp_max - 1)
		{
		  pass_on_reg (regcache, gp++, val, rlen);
		  pass_on_reg (regcache, gp++, val + rlen, len - rlen);
		}
	      else
		pass_on_stack (stack, val, len, rlen);
	    }
	  break;
	case TYPE_CODE_ARRAY:
	  /* lsx */
	  if (TYPE_VECTOR (a_type) && len == vec_insn && vec_insn == 16
	      && fp < fp_max)
	    {
	      pass_on_reg (regcache, regs->vr + (fp++ - regs->f), val, len);
	    }
	  /* lasx */
	  else if (TYPE_VECTOR (a_type) && len == vec_insn && vec_insn == 32
		   && fp < fp_max)
	    {
	      pass_on_reg (regcache, regs->xr + (fp++ - regs->f), val, len);
	    }
	  /* scalar */
	  else
	    {
	      if (len > rlen * 2)
		{
		  /* Address on register, data on stack.  */
		  sp = align_down (sp - len, rlen);
		  write_memory (sp, val, len);
		  if (gp < gp_max)
		    pass_on_reg (regcache, gp++, (const gdb_byte *) &sp, rlen);
		  else
		    pass_on_stack (stack, (const gdb_byte *) sp, rlen, rlen,
				   true);
		}
	      else
		{
		  if (len <= rlen && gp < gp_max)
		    {
		      pass_on_reg (regcache, gp++, val, len);
		    }
		  else if (gp + 1 < gp_max)
		    {
		      pass_on_reg (regcache, gp++, val, rlen);
		      pass_on_reg (regcache, gp++, val + rlen, rlen);
		    }
		  else
		    {
		      pass_on_stack (stack, val, len, rlen);
		    }
		}
	    }
	  break;
	case TYPE_CODE_STRUCT:
	case TYPE_CODE_UNION:
	  if (len > rlen * 2)
	    {
	      /* Address on register, data on stack.  */
	      sp = align_down (sp - len, rlen);
	      write_memory (sp, val, len);
	      if (gp < gp_max)
		pass_on_reg (regcache, gp++, (const gdb_byte *) &sp, rlen);
	      else
		pass_on_stack (stack, (const gdb_byte *) sp, rlen, rlen, true);
	    }
	  else
	    {
	      if (!try_pass_small_struct_on_reg (gdbarch, regcache, arg, gp,
						 fp, gp_max, fp_max))
		{
		  pass_on_stack (stack, val, len, rlen);
		}
	    }
	  break;
	case TYPE_CODE_COMPLEX:
	  {
	    /* Two fpr or  mem.  */
	    struct type *t_type = check_typedef (TYPE_TARGET_TYPE (a_type));
	    int tlen = TYPE_LENGTH (t_type);

	    if (tlen < rlen)
	      {
		if (!TYPE_VARARGS (f_type) && fp + 1 < fp_max)
		  {
		    pass_on_reg (regcache, fp++, (const gdb_byte *) val, tlen);
		    pass_on_reg (regcache, fp++, (const gdb_byte *) val + tlen,
				 tlen);
		  }
		else if (gp < gp_max)
		  {
		    pass_on_reg (regcache, gp++, (const gdb_byte *) val, rlen);
		  }
		else
		  {
		    pass_on_stack (stack, val, len, rlen);
		  }
	      }
	    else if (tlen == rlen)
	      {
		if (!TYPE_VARARGS (f_type) && fp + 1 < fp_max)
		  {
		    pass_on_reg (regcache, fp++, (const gdb_byte *) val, tlen);
		    pass_on_reg (regcache, fp++, (const gdb_byte *) val + tlen,
				 tlen);
		  }
		else if (gp + 1 < gp_max)
		  {
		    pass_on_reg (regcache, gp++, (const gdb_byte *) val, rlen);
		    pass_on_reg (regcache, gp++, (const gdb_byte *) val + rlen,
				 rlen);
		  }
		else if (gp + 1 == gp_max)
		  {
		    pass_on_reg (regcache, gp++, (const gdb_byte *) val, rlen);
		    pass_on_stack (stack, val, tlen, rlen);
		  }
		else
		  {
		    pass_on_stack (stack, val, len, rlen);
		  }
	      }
	    else
	      {
		sp = align_down (sp - len, rlen);
		write_memory (sp, val, len);
		if (gp < gp_max)
		  pass_on_reg (regcache, gp++, (const gdb_byte *) &sp, rlen);
		else
		  {
		    pass_on_stack (stack, (const gdb_byte *) sp, rlen, rlen,
				   true);
		  }
	      }
	  }
	  break;
	default:
	  break;
	}
    }

  for (auto it : stack)
    sp = align_down (sp - it.len, rlen);

  sp = align_down (sp, 16);
  CORE_ADDR tsp = sp;
  for (auto it : stack)
    {
      if (it.ref)
	write_memory (tsp, (const gdb_byte *) &it.addr, it.len);
      else
	write_memory (tsp, it.addr, it.len);
      tsp += it.len;
      stack.pop_back ();
    }
  regcache_cooked_write_unsigned (regcache, regs->sp, sp);
  return sp;
}

static void
loongarch_xfer_reg_part (struct regcache *regcache, int reg_num, int len,
			 gdb_byte *readbuf, size_t readbuf_off,
			 const gdb_byte *writebuf, size_t writebuf_off)
{
  if (readbuf)
    regcache->cooked_read_part (reg_num, 0, len, readbuf + readbuf_off);
  if (writebuf)
    regcache->cooked_write_part (reg_num, 0, len, writebuf + writebuf_off);
}

static enum return_value_convention
loongarch_lp64_return_value (struct gdbarch *gdbarch, struct value *function,
			     struct type *type, struct regcache *regcache,
			     gdb_byte *readbuf, const gdb_byte *writebuf)
{
  const size_t rlen = loongarch_rlen (gdbarch) / 8;
  auto regs = &gdbarch_tdep (gdbarch)->regs;
  size_t len = TYPE_LENGTH (type);
  enum type_code typecode = type->code ();
  int fpu_exist = 0 <= regs->f;
  int fv = fpu_exist ? regs->f : regs->r + 4;

  gdb_assert (8 <= sizeof (LONGEST));

  gdb_assert (!fpu_exist || register_size (gdbarch, regs->f) == rlen);

  if (2 * rlen < len)
    return RETURN_VALUE_STRUCT_CONVENTION;

  if (((typecode == TYPE_CODE_INT && TYPE_UNSIGNED (type))
	    || typecode == TYPE_CODE_ENUM)
	   && len <= rlen)
    /* For unsigned scalar type, we have zero-extended one in $v0.  */
    if (writebuf)
      {
	gdb_byte buf[rlen];
	store_signed_integer (buf, rlen, BFD_ENDIAN_LITTLE,
			      extract_unsigned_integer (writebuf, len,
							BFD_ENDIAN_LITTLE));
	loongarch_xfer_reg_part (regcache, regs->r + 4, rlen, NULL, 0,
				 writebuf, 0);
      }
    else
      loongarch_xfer_reg_part (regcache, regs->r + 4, len, readbuf, 0, NULL,
			       0);
  else if (((typecode == TYPE_CODE_INT && !TYPE_UNSIGNED (type))
	    || typecode == TYPE_CODE_PTR)
	   && len <= rlen)
    /* For signed scalar type, we have sign-extended one in $v0.  */
    if (writebuf)
      {
	gdb_byte buf[rlen];
	store_signed_integer (buf, rlen, BFD_ENDIAN_LITTLE,
			      extract_signed_integer (writebuf, len,
						      BFD_ENDIAN_LITTLE));
	loongarch_xfer_reg_part (regcache, regs->r + 4, rlen, NULL, 0,
				 writebuf, 0);
      }
    else
      loongarch_xfer_reg_part (regcache, regs->r + 4, len, readbuf, 0, NULL,
			       0);
  else
    {
      int complex_num = 0, float_num = 0, other_num = 0;
      int counter = 0, float_seq = 0, other_seq = 0, tlen;
      /* Calculate the relevant members and types in the return value
         and mark them.  */
      compute_type_num(type, complex_num, float_num, other_num,
		       counter, float_seq, other_seq);

      if (len == rlen)
        tlen = rlen / 2;
      else
        tlen = rlen;

      /* For the small structure has only other types members (like char/short/int/long
         etc.), and the size does not exceed rlen, pass on $v0.  */
      /* For 'char/short/int/long' etc. pass on $v0.  */
      if (other_num > 0 && float_num == 0 && len <= rlen)
	loongarch_xfer_reg_part (regcache, regs->r + 4, len, readbuf, 0,
				 writebuf, 0);
      /* For small structure with only one floating-point member, (like float/double) pass on $fv0.  */
      /* For float/double pass on $fv0.  */
      else if (float_num == 1 && complex_num == 0 && other_num == 0 && len <= rlen)
	loongarch_xfer_reg_part (regcache, fv, len, readbuf, 0, writebuf, 0);
      /* For small structure with one float/double member and one other member
	 (char/short/int/long etc.). If the float/dobule member is in the front
	 position, the float/dobule member pass on $fv0, the other member pass
	 on $v0, otherwise the opposite .  */
      else if (float_num == 1 && other_num == 1)
	if (float_seq < other_seq)
	  loongarch_xfer_reg_part (regcache, fv, rlen, readbuf, 0,
				   writebuf, 0),
	    loongarch_xfer_reg_part (regcache, regs->r + 4, tlen, readbuf,
				     tlen, writebuf, rlen);
	else
	  loongarch_xfer_reg_part (regcache, regs->r + 4, rlen, readbuf, 0,
				   writebuf, 0),
	    loongarch_xfer_reg_part (regcache, fv, tlen, readbuf,
				     tlen, writebuf, rlen);
      /* For small structure with one 'float/double _Complex' member,
         $fv0 is real and $fv1 is img.   */
      /* For small structure with only one float and double member or
	 or two float member , or two dobule member, $fv0 is the 1st
	 member and $fv1 is the 2nd member.  */
      /* For 'float/double _Complex', $fv0 is real and $fv1 is img.  */
      else if ((complex_num == 1 && float_num == 0 && other_num == 0) ||
	       (float_num ==2 && other_num == 0))
	loongarch_xfer_reg_part (regcache, fv, rlen, readbuf, 0,
				 writebuf, 0),
	  loongarch_xfer_reg_part (regcache, fv + 1, tlen, readbuf,
				   tlen, writebuf, rlen);
     /* For small structure with 'long double' member,
	or when the small structure has more than two vaild members
	and the size is greater than rlen, pass on $v0 and $v1.  */
     /* For small structure with two 'float _Complex' member,
	$v0 is the 1st member and $v1 is the 2nd member.  */
     /* For 'long double' on fpu64 or 'double' on fpu32 pass on $v0 and $v1.  */
      else
	loongarch_xfer_reg_part (regcache, regs->r + 4, rlen, readbuf, 0,
				 writebuf, 0),
	  loongarch_xfer_reg_part (regcache, regs->r + 5, len - rlen, readbuf,
				   rlen, writebuf, rlen);
    }

  return RETURN_VALUE_REGISTER_CONVENTION;
}

static int
loongarch_dwarf2_reg_to_regnum (struct gdbarch *gdbarch, int num)
{
  auto regs = &gdbarch_tdep (gdbarch)->regs;
  if (0 <= num && num < 32)
    return regs->r + num;
  else if (32 <= num && num < 64 && 0 <= regs->f)
    return regs->f + num - 32;
  else if (64 <= num && num < 72 && 0 <= regs->fcc)
    return regs->fcc + num - 64;
  else
    return -1;
}

static std::string
loongarch_gcc_target_options (struct gdbarch *gdbarch)
{
  return "";
}

static int
loongarch_register_reggroup_p (struct gdbarch *gdbarch, int regnum,
			       struct reggroup *group)
{
  auto regs = &gdbarch_tdep (gdbarch)->regs;

  if (gdbarch_register_name (gdbarch, regnum) == NULL
      || *gdbarch_register_name (gdbarch, regnum) == '\0')
    return 0;

  int raw_p = regnum < gdbarch_num_regs (gdbarch);

  if (group == save_reggroup || group == restore_reggroup)
    return raw_p;
  if (group == all_reggroup)
    return 1;

  if (group == general_reggroup
      && (regs->orig_a0 == regnum || regs->pc == regnum
	  || regs->badv == regnum
	  || (regs->r <= regnum && regnum < regs->r + 32)))
    return 1;

  /* Only $rx and $pc in general_reggroup.  */
  if (group == general_reggroup)
    return 0;

  if (0 <= regs->f
      && (regs->fcsr == regnum || (regs->f <= regnum && regnum < regs->f + 32)
	  || (regs->fcc <= regnum && regnum < regs->fcc + 8)))
    return group == float_reggroup;

  /* Only $fx / $fccx / $fcsr in float_reggroup.  */
  if (group == float_reggroup)
    return 0;

  if (0 <= regs->vr && regs->vr <= regnum && regnum < regs->vr + 32)
    if (group == vector_reggroup)
      return 1;

  if (0 <= regs->xr && regs->xr <= regnum && regnum < regs->xr + 32)
    if (group == vector_reggroup)
      return 1;

  int ret = tdesc_register_in_reggroup_p (gdbarch, regnum, group);
  if (ret != -1)
    return ret;

  return default_register_reggroup_p (gdbarch, regnum, group);
}

constexpr gdb_byte loongarch_default_breakpoint[] = {0x05, 0x00, 0x2a, 0x00};
typedef BP_MANIPULATION (loongarch_default_breakpoint) loongarch_breakpoint;

/* Initialize the current architecture based on INFO.  If possible,
   re-use an architecture from ARCHES, which is a list of
   architectures already created during this debugging session.

   Called e.g. at program startup, when reading a core file, and when
   reading a binary file.  */

/* This predicate tests whether we need to read lsx/lasx registers
   (instead of fp registers with the same DWARF2 code
   (thus the same internal code, though lasx/lsx/fp reg internal
   codes are different)) according to the byte-size of requested type.  */

static int
loongarch_fp_regnum_refers_to_lsx_lasx_p (struct gdbarch *gdbarch, int regnum,
					  struct type *type)
{
  /* Conditions:
       1) regnum is in "disputed" zone (fp/lsx/lasx, translated
	  from dwarf regnum).
       2) type is larger than 8 bytes.

      (if specified type is larger than 8 bytes,
       then regnum refers to lsx / lasx register instead of fp register).
    */
  return regnum >= gdbarch_tdep (gdbarch)->regs.f
	 && regnum < gdbarch_tdep (gdbarch)->regs.f + 32
	 && TYPE_LENGTH (type) > 8;
}

static int
loongarch_convert_register_p (struct gdbarch *gdbarch, int regnum,
			      struct type *type)
{
  return loongarch_fp_regnum_refers_to_lsx_lasx_p (gdbarch, regnum, type);
}

static int
loongarch_register_to_value (struct frame_info *frame, int regnum,
			     struct type *type, gdb_byte *to, int *optimizedp,
			     int *unavailablep)
{
  struct gdbarch *gdbarch = get_frame_arch (frame);

  if (loongarch_fp_regnum_refers_to_lsx_lasx_p (gdbarch, regnum, type))
    {
      /* Add a displacement to regnum.  */
      switch (TYPE_LENGTH (type))
	{
	case 16: /* 16-byte types, access vr.  */
	  if (!get_frame_register_bytes (frame,
					 regnum
					   + gdbarch_tdep (gdbarch)->regs.vr
					   - gdbarch_tdep (gdbarch)->regs.f,
					 0, 16, to + 0, optimizedp,
					 unavailablep))
	    return 0;
	  break;

	case 32: /* 32-byte types, access xr.  */
	  if (!get_frame_register_bytes (frame,
					 regnum
					   + gdbarch_tdep (gdbarch)->regs.xr
					   - gdbarch_tdep (gdbarch)->regs.f,
					 0, 32, to + 0, optimizedp,
					 unavailablep))
	    return 0;
	  break;

	default:
	  goto fail;
	}

      *optimizedp = *unavailablep = 0;
      return 1; /* 1 for success, 0 for fail.  */
    }

fail:
  internal_error (__FILE__, __LINE__,
		  _ ("loongarch_register_to_value: unrecognized case"));
}

static void
loongarch_value_to_register (struct frame_info *frame, int regnum,
			     struct type *type, const gdb_byte *from)
{
  struct gdbarch *gdbarch = get_frame_arch (frame);
  if (loongarch_fp_regnum_refers_to_lsx_lasx_p (gdbarch, regnum, type))
    {
      switch (TYPE_LENGTH (type))
	{
	case 16: /* 16-byte types, access vr.  */
	  put_frame_register (frame,
			      regnum + gdbarch_tdep (gdbarch)->regs.vr
				- gdbarch_tdep (gdbarch)->regs.f,
			      from);
	  return;

	case 32: /* 32-byte types, access xr.  */
	  put_frame_register (frame,
			      regnum + gdbarch_tdep (gdbarch)->regs.xr
				- gdbarch_tdep (gdbarch)->regs.f,
			      from);
	  return;
	}
    }

  internal_error (__FILE__, __LINE__,
		  _ ("loongarch_value_to_register: unrecognized case"));
}

static int
loongarch_get_longjmp_target (struct frame_info *frame, CORE_ADDR *pc)
{
  CORE_ADDR jb_addr;
  struct gdbarch *gdbarch = get_frame_arch (frame);
  uint32_t ptr_size = gdbarch_ptr_bit (gdbarch) / TARGET_CHAR_BIT;
  gdb_byte buf[ptr_size];

  jb_addr = get_frame_register_unsigned (frame, LOONGARCH_A0_REGNUM);

  if (target_read_memory ((jb_addr + LOONGARCH_JB_PC * ptr_size),
                          buf, ptr_size))
    return 0;

  *pc = extract_unsigned_integer (buf, ptr_size, BFD_ENDIAN_LITTLE);

  return 1;
}

static struct gdbarch *
loongarch_gdbarch_init (struct gdbarch_info info, struct gdbarch_list *arches)
{
  struct gdbarch *gdbarch;
  struct gdbarch_tdep tdep_instant, *tdep;
  struct tdesc_arch_data *tdesc_data = NULL;
  const struct target_desc *tdesc = info.target_desc;
  int i;
  size_t regnum;

  tdep = &tdep_instant;
  memset (tdep, 0, sizeof (*tdep));
  memset (&tdep->regs, -1, sizeof (tdep->regs));

  /* If abfd is nullptr then a EF_LOONGARCH_ABI_LP64 | EF_LOONGARCH_FLOAT_ABI_DOUBLE
     is returned in its default state.  */
  if (info.abfd != NULL
      && bfd_get_flavour (info.abfd) == bfd_target_elf_flavour)
    {
      int eflags = elf_elfheader (info.abfd)->e_flags;
      unsigned char eclass = elf_elfheader (info.abfd)->e_ident[EI_CLASS];

      if (eflags) /* Executable file */
	{
	  tdep->ef_abi = (EF_LOONGARCH_ABI(eflags) & EF_LOONGARCH_ABI_MASK);
	}
      else /* Core file */
	{
	  if (eclass == ELFCLASS64)
	    tdep->ef_abi = EF_LOONGARCH_ABI_LP64_DOUBLE_FLOAT;
	  else
	    tdep->ef_abi = EF_LOONGARCH_ABI_ILP32_DOUBLE_FLOAT;
	}
    }
  else
    tdep->ef_abi = EF_LOONGARCH_ABI_LP64_DOUBLE_FLOAT;

  /* Check any target description for validity.  */
  if (!tdesc_has_registers (tdesc))
    tdesc = loongarch_get_base_target_description (
      EF_LOONGARCH_IS_ILP32 (tdep->ef_abi) ? 32 : 64,
      EF_LOONGARCH_IS_SINGLE_FLOAT (tdep->ef_abi) ? 32 : 64);

  int valid_p = 1;
  const struct tdesc_feature *feature;

  feature = tdesc_find_feature (tdesc, "org.gnu.gdb.loongarch.base");
  if (feature == NULL)
    return NULL;
  regnum = 0;
  tdesc_data = tdesc_data_alloc ();

  tdep->regs.r = regnum;
  for (i = 0; i < 32; i++)
    valid_p &= tdesc_numbered_register (feature, tdesc_data, regnum++,
					loongarch_r_normal_name[i] + 1);
  valid_p &= tdesc_numbered_register (feature, tdesc_data,
				      tdep->regs.orig_a0 = regnum++, "orig_a0");
  valid_p &= tdesc_numbered_register (feature, tdesc_data,
				      tdep->regs.pc = regnum++, "pc");
  valid_p
    &= tdesc_numbered_register (feature, tdesc_data,
				tdep->regs.badv = regnum++, "badv");

  if ((feature = tdesc_find_feature (tdesc, "org.gnu.gdb.loongarch.fpu")))
    {
      tdep->regs.f = regnum;
      for (i = 0; i < 32; i++)
	valid_p
	  &= tdesc_numbered_register (feature, tdesc_data, regnum++,
				      loongarch_f_normal_name[i] + 1);
      tdep->regs.fcc = regnum;
      valid_p &= tdesc_numbered_register (feature, tdesc_data, regnum++,
					  "fcc0");
      valid_p &= tdesc_numbered_register (feature, tdesc_data, regnum++,
					  "fcc1");
      valid_p &= tdesc_numbered_register (feature, tdesc_data, regnum++,
					  "fcc2");
      valid_p &= tdesc_numbered_register (feature, tdesc_data, regnum++,
					  "fcc3");
      valid_p &= tdesc_numbered_register (feature, tdesc_data, regnum++,
					  "fcc4");
      valid_p &= tdesc_numbered_register (feature, tdesc_data, regnum++,
					  "fcc5");
      valid_p &= tdesc_numbered_register (feature, tdesc_data, regnum++,
					  "fcc6");
      valid_p &= tdesc_numbered_register (feature, tdesc_data, regnum++,
					  "fcc7");
      valid_p &= tdesc_numbered_register (feature, tdesc_data,
					  tdep->regs.fcsr = regnum++, "fcsr");
    }

  if ((feature = tdesc_find_feature (tdesc, "org.gnu.gdb.loongarch.lbt")))
    {
      tdep->regs.scr = regnum;
      for (i = 0; i < 4; i++)
	valid_p
	  &= tdesc_numbered_register (feature, tdesc_data, regnum++,
				      loongarch_cr_normal_name[i] + 1);
      valid_p
	&= tdesc_numbered_register (feature, tdesc_data,
				    tdep->regs.EFLAG = regnum++, "EFLAG");
      valid_p
	&= tdesc_numbered_register (feature, tdesc_data,
				    tdep->regs.x86_top = regnum++, "x86_top");
    }

  if ((feature = tdesc_find_feature (tdesc, "org.gnu.gdb.loongarch.lsx")))
    {
      tdep->regs.vr = regnum;
      for (i = 0; i < 32; i++)
	valid_p
	  &= tdesc_numbered_register (feature, tdesc_data, regnum++,
				      loongarch_v_normal_name[i] + 1);
    }

  if ((feature = tdesc_find_feature (tdesc, "org.gnu.gdb.loongarch.lasx")))
    {
      tdep->regs.xr = regnum;
      for (i = 0; i < 32; i++)
	valid_p
	  &= tdesc_numbered_register (feature, tdesc_data, regnum++,
				      loongarch_x_normal_name[i] + 1);
    }

  if (!valid_p)
    {
      return NULL;
    }

  info.byte_order_for_code = BFD_ENDIAN_LITTLE;

  /* Find a candidate among the list of pre-declared architectures.  */
  for (arches = gdbarch_list_lookup_by_info (arches, &info); arches != NULL;
       arches = gdbarch_list_lookup_by_info (arches->next, &info))
    {
      if (gdbarch_tdep (arches->gdbarch)->ef_abi != tdep->ef_abi)
	continue;

      return arches->gdbarch;
    }

  /* None found, so create a new architecture from the information provided. */
  tdep = (struct gdbarch_tdep *) xmalloc (sizeof (tdep_instant));
  memcpy (tdep, &tdep_instant, sizeof (tdep_instant));
  gdbarch = gdbarch_alloc (&info, tdep);

  /* Target data types.  */
  if (EF_LOONGARCH_IS_ILP32 (tdep->ef_abi))
    {
      set_gdbarch_short_bit (gdbarch, 16);
      set_gdbarch_int_bit (gdbarch, 32);
      set_gdbarch_long_bit (gdbarch, 32);
      set_gdbarch_long_long_bit (gdbarch, 32);
      set_gdbarch_float_bit (gdbarch, 32);
      set_gdbarch_double_bit (gdbarch, 64);
      set_gdbarch_long_double_bit (gdbarch, 128);
      set_gdbarch_long_double_format (gdbarch, floatformats_ia64_quad);
      set_gdbarch_ptr_bit (gdbarch, 32);
      set_gdbarch_char_signed (gdbarch, 0);
    }
  else if (EF_LOONGARCH_IS_LP64 (tdep->ef_abi))
    {
      set_gdbarch_short_bit (gdbarch, 16);
      set_gdbarch_int_bit (gdbarch, 32);
      set_gdbarch_long_bit (gdbarch, 64);
      set_gdbarch_long_long_bit (gdbarch, 64);
      set_gdbarch_float_bit (gdbarch, 32);
      set_gdbarch_double_bit (gdbarch, 64);
      set_gdbarch_long_double_bit (gdbarch, 128);
      set_gdbarch_long_double_format (gdbarch, floatformats_ia64_quad);
      set_gdbarch_ptr_bit (gdbarch, 64);
      set_gdbarch_char_signed (gdbarch, 0);

      tdep->regs.ra = tdep->regs.r + 1;
      tdep->regs.sp = tdep->regs.r + 3;

      for (i = 0; i < ARRAY_SIZE (loongarch_r_normal_name); ++i)
	if (loongarch_r_normal_name[i][0] != '\0')
	  user_reg_add (gdbarch, loongarch_r_normal_name[i] + 1,
			value_of_loongarch_user_reg,
			(void *) (size_t) (tdep->regs.r + i));

      for (i = 0; i < ARRAY_SIZE (loongarch_r_lp64_name); ++i)
	if (loongarch_r_lp64_name[i][0] != '\0')
	  user_reg_add (gdbarch, loongarch_r_lp64_name[i] + 1,
			value_of_loongarch_user_reg,
			(void *) (size_t) (tdep->regs.r + i));

      for (i = 0; i < ARRAY_SIZE (loongarch_r_lp64_name1); ++i)
	if (loongarch_r_lp64_name[i][0] != '\0')
	  user_reg_add (gdbarch, loongarch_r_lp64_name1[i] + 1,
			value_of_loongarch_user_reg,
			(void *) (size_t) (tdep->regs.r + i));

      /* Functions handling dummy frames.  */
      set_gdbarch_push_dummy_call (gdbarch,
				   loongarch_lp32lp64_push_dummy_call);
      set_gdbarch_return_value (gdbarch, loongarch_lp64_return_value);

    }
  else
    gdb_assert_not_reached ("unknown ABI");

  /* Hook in OS ABI-specific overrides, if they have been registered.  */
  info.target_desc = tdesc;
  info.tdesc_data = tdesc_data;

  /* Register architecture.  */
  set_gdbarch_num_regs (gdbarch, regnum);
  set_gdbarch_sp_regnum (gdbarch, tdep->regs.sp);
  set_gdbarch_pc_regnum (gdbarch, tdep->regs.pc);

  tdesc_use_registers (gdbarch, tdesc, std::move (tdesc_data));

  /* Functions to supply register information.  */
  set_gdbarch_register_name (gdbarch, loongarch_register_name);

  /* Handle overlapping dwarf2 register code for fp/lsx/lasx.  */
  set_gdbarch_convert_register_p (gdbarch, loongarch_convert_register_p);
  set_gdbarch_register_to_value (gdbarch, loongarch_register_to_value);
  set_gdbarch_value_to_register (gdbarch, loongarch_value_to_register);

  /* Functions to analyze frames.  */
  set_gdbarch_skip_prologue (gdbarch, loongarch_skip_prologue);
  set_gdbarch_inner_than (gdbarch, core_addr_lessthan);
  set_gdbarch_frame_align (gdbarch, loongarch_frame_align);

  /* Functions to access frame data.  */
  set_gdbarch_unwind_pc (gdbarch, loongarch_unwind_pc);
  set_gdbarch_unwind_sp (gdbarch, loongarch_unwind_sp);

  set_gdbarch_dummy_id (gdbarch, loongarch_dummy_id);

  set_gdbarch_software_single_step (gdbarch, loongarch_software_single_step);

  set_gdbarch_breakpoint_kind_from_pc (gdbarch,
				       loongarch_breakpoint::kind_from_pc);
  set_gdbarch_sw_breakpoint_from_kind (gdbarch,
				       loongarch_breakpoint::bp_from_kind);

  set_gdbarch_have_nonsteppable_watchpoint (gdbarch, 1);

  /* Virtual tables.  */
  set_gdbarch_vbit_in_delta (gdbarch, 1);

  set_gdbarch_gcc_target_options (gdbarch, loongarch_gcc_target_options);

  gdbarch_init_osabi (info, gdbarch);
  set_gdbarch_register_reggroup_p (gdbarch, loongarch_register_reggroup_p);
  set_gdbarch_register_name (gdbarch, loongarch_register_name);

  set_gdbarch_get_longjmp_target (gdbarch, loongarch_get_longjmp_target);

  /* Frame unwinders.  Use DWARF debug info if available, otherwise use our own
     unwinder.  */
  set_gdbarch_dwarf2_reg_to_regnum (gdbarch, loongarch_dwarf2_reg_to_regnum);
  dwarf2_append_unwinders (gdbarch);
  frame_unwind_append_unwinder (gdbarch, &loongarch_frame_unwind);

  return gdbarch;
}

static void
info_loongarch (const char *addr_exp, int from_tty)
{
  char *buf, *t;
  int set;
  char *item;
  unsigned long addr;
  unsigned long long value;

  if (addr_exp)
    {
      addr_exp = skip_spaces (addr_exp);
      buf = (char *) alloca (strlen (addr_exp) + 1);
      strcpy (buf, addr_exp);
      loongarch_eliminate_adjacent_repeat_char (buf, ' ');
    }
  else
    goto Empty;

  if (!(t = strtok (buf, " ")))
    goto Empty;
  if (strcmp (t, "set") == 0)
    {
      t = strtok (NULL, " ");
      set = 1;
    }
  else
    {
      if (strcmp (t, "get") == 0)
	t = strtok (NULL, " ");
      set = 0;
    }
  if (!(item = t))
    goto Empty;
  if (!(t = strtok (NULL, " ")))
    goto Empty;
  addr = strtoul (t, NULL, 0);
  if (set && (t = strtok (NULL, " ")) == NULL)
    goto Empty;
  value = strtoll (t, NULL, 0);

  if (set)
    if (strcmp (item, "cpucfg") == 0)
      {
	uint32_t val32 = value;
	ULONGEST xfered_len;
	target_xfer_partial (current_inferior ()->top_target (),
			     TARGET_OBJECT_LARCH, "cpucfg", NULL,
			     (const gdb_byte *) &val32, addr * 4,
			     sizeof (val32), &xfered_len);
	if (0 < xfered_len)
	  fprintf_unfiltered (gdb_stdout, "ok\n");
	else
	  error ("Set failed");
      }
    else
      {
	uint64_t val64 = value;
	ULONGEST xfered_len;
	target_xfer_partial (current_inferior ()->top_target (),
			     TARGET_OBJECT_LARCH, item, NULL,
			     (const gdb_byte *) &val64, addr * 8,
			     sizeof (val64), &xfered_len);
	if (0 < xfered_len)
	  fprintf_unfiltered (gdb_stdout, "ok\n");
	else
	  error ("Set failed");
      }
  else if (strcmp (item, "cpucfg") == 0)
    {
      uint32_t val32;
      ULONGEST xfered_len;
      target_xfer_partial (current_inferior ()->top_target (),
			   TARGET_OBJECT_LARCH, "cpucfg", (gdb_byte *) &val32,
			   NULL, addr * 4, sizeof (val32), &xfered_len);
      if (0 < xfered_len)
	fprintf_unfiltered (gdb_stdout, "return is %x\n", val32);
      else
	error ("Get failed");
    }
  else
    {
      uint64_t val64;
      ULONGEST xfered_len;
      target_xfer_partial (current_inferior ()->top_target (),
			   TARGET_OBJECT_LARCH, item, (gdb_byte *) &val64,
			   NULL, addr * 8, sizeof (val64), &xfered_len);
      if (0 < xfered_len)
	fprintf_unfiltered (gdb_stdout, "return is %llx\n", (long long) val64);
      else
	error ("Get failed");
    }

  return;
Empty:
  error ("Empty. Should be 'info loongarch ([get]|set) item addr [value]'");
}

void _initialize_loongarch_tdep ();
void
_initialize_loongarch_tdep ()
{
  gdbarch_register (bfd_arch_loongarch, loongarch_gdbarch_init, NULL);

  add_info ("loongarch", info_loongarch, _ ("Loongarch extra"));

  /* Debug this files internals.  */
  add_setshow_zuinteger_cmd ("loongarch", class_maintenance, &loongarch_debug,
			     _ ("\
Set loongarch debugging."),
			     _ ("\
Show loongarch debugging."),
			     _ ("\
When non-zero, loongarch specific debugging is enabled."),
			     NULL, NULL, &setdebuglist, &showdebuglist);
}
