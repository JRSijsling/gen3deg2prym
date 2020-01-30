/***
 *  Actual interpolation
 *
 *  Copyright (C) 2019
 *            Jeroen Sijsling  (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

load "ghs.m";
load "coeffss.m";

d := 4;
R<g2,g1,g0,h2,h1,h0> := PolynomialRing(Rationals(), 6);
K<g2,g1,g0,h2,h1,h0> := FieldOfFractions(R);

rats := [ ];
for i:=1 to #coeffss[1] do
    print "";
    print i;
    mons := &cat[ [ mon : mon in MonomialsOfDegree(R, i) ] : i in [0..d] ];
    seq := [ ];
    for j:=1 to #ghs do;
        row1 := [                Evaluate(mon, ghs[j]) : mon in mons ];
        row2 := [ -coeffss[j][i]*Evaluate(mon, ghs[j]) : mon in mons ];
        Append(~seq, row1 cat row2);
    end for;
    M := Matrix(Rationals(), seq);
    K := Kernel(Transpose(M));
    B := Basis(K);
    v := Eltseq(B[1]);

    num := &+[ v[i]*mons[i] : i in [1..#mons] ];
    den := &+[ v[#mons + i]*mons[i] : i in [1..#mons] ];
    rat := num/den;
    print rat;
    print Factorization(Numerator(rat));
    print Factorization(Denominator(rat));
    Append(~rats, rat);
end for;
print rats;

