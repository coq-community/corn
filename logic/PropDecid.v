(* Copyright  2008-2008
 * Cezary Kaliszyk
 * Russell O'Connor
 *
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

(**
** Decidability of connectives
Here we show the decidability of logical connectives.
*)

Lemma imp_dec : (forall A B, ({A} + {~A}) -> ({B} + {~B}) -> ({A -> B} + {~(A -> B)})).
tauto.
Qed.

(* TODO: other connectives *)