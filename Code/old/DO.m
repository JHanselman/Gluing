/***
 *  Generating random examples of reconstruction
 *
 *  Distributed under the terms of the GNU Lesser General Public License (L-GPL)
 *                  http://www.gnu.org/licenses/
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation; either version 2.1 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 *  Copyright 2016 R. Lercier, C. Ritzenthaler & J.R. Sijsling
 */

AttachSpec("package/spec");
AttachSpec("g3twists_v2-0/spec");

SetVerbose("Reconstruction", 1);
SetVerbose("G3Twists", 1);
SetVerbose("PlaneQuartic", 1);
SetVerbose("ClusterReduction", 1);

/* Start from a random ternary quartic */
F := Rationals();  B := 2^10; Domain := [-B..B];
//q := NextPrime(10^103);
//F := GF(q);  Domain := F;

DOf := [ 476763642, 108015304423391865, 7814149185868071494153403906,
4992808769799831000669733902, 3899824330183202437635711786793717500,
31790893720375267411424585443873756884,
8972404330872539651571842414733601309237495770,
2974241880339068601294746936760086536716908310,
15548689698692129585243213068237250960717726374595088300,
17845308557589711719806838756754592148199207712399646700,
63008953703716407837984635325925826000706282552824834974451457120,
1091285035441560215078256132976925058166720356923223003314034784200,
15807267536350228260374426581978488339572475049219730011172039274853407129600000000
];
DOf := [ F ! DO : DO in DOf ];

/* Construct another quartic with equivalent invariants */
g, aut, twists := TernaryQuarticFromDixmierOhnoInvariants(DOf);
_<x1,x2,x3> := Parent(g);
print "";
print "The reconstructed curve is g =", g;
print "Automorphism group", aut;

DOg, W := DixmierOhnoInvariants(g);
print WPSNormalize(W, DOg) eq WPSNormalize(W, DOf);
