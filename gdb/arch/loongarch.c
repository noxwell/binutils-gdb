/* Copyright (C) 2021 Free Software Foundation, Inc.

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

#include "gdbsupport/common-defs.h"
#include "gdbsupport/common-regcache.h"
#include "arch/loongarch.h"

unsigned int loongarch_debug = 0;

#include <../features/loongarch/base32.c>
#include <../features/loongarch/base64.c>
#include <../features/loongarch/fpu32.c>
#include <../features/loongarch/fpu64.c>
#include <../features/loongarch/lbt32.c>
#include <../features/loongarch/lbt64.c>
#include <../features/loongarch/lsx.c>
#include <../features/loongarch/lasx.c>

target_desc *
loongarch_create_target_description (int rlen, int flen, int lbt,
				     int lsx, int lasx)
{
  gdb_assert (rlen == 32 || rlen == 64);

  target_desc *tdesc = allocate_target_description ();

  set_tdesc_architecture (tdesc, rlen == 64 ? "loongarch64" : "loongarch32");

  int regnum = 0;

  if (rlen == 64)
    regnum = create_feature_loongarch_base64 (tdesc, regnum);
  else if (rlen == 32)
    regnum = create_feature_loongarch_base32 (tdesc, regnum);
  else
    gdb_assert_not_reached ("rlen unknown");

  if (flen == 64)
    regnum = create_feature_loongarch_fpu64 (tdesc, regnum);
  else if (flen == 32)
    regnum = create_feature_loongarch_fpu32 (tdesc, regnum);

  if (lbt && rlen == 32)
    regnum = create_feature_loongarch_lbt32 (tdesc, regnum);
  else if (lbt && rlen == 64)
    regnum = create_feature_loongarch_lbt64 (tdesc, regnum);

  if (lsx)
    regnum = create_feature_loongarch_lsx (tdesc, regnum);

  if (lasx)
    regnum = create_feature_loongarch_lasx (tdesc, regnum);

  return tdesc;
}

target_desc *
loongarch_get_base_target_description (int rlen, int flen)
{
    return loongarch_create_target_description (rlen, flen, 0, 0, 0);
}
