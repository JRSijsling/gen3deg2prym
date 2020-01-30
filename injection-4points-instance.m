/***
 *  Proves that X --> Jac (Y) is injective
 *
 *  Copyright (C) 2019
 *            Jeroen Sijsling  (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

F := FiniteField(19);
F := Rationals();

K<g1,g0,h1,h0> := RationalFunctionField(F, 4);
g2 := 1; h2 := 1;
K := F;
D := [-7..7];

done := false;
while not done do
    g1 := Random(D); g0 := Random(D); h1 := Random(D); h0 := Random(D);
    g1 := -4; g0 := -6; h1 := -4; h0 := -5;

    S<x,y,z> := PolynomialRing(K, 3);
    G := y^2 + g1*y*z + g0*z^2;
    H := y^2 + h1*y*z + h0*z^2;
    F := x^4 + x^2*G + y*z*H;

    X := PlaneCurve(F);
    Ps := Points(X);
    if not (IsNonSingular(X) and #Ps gt 2) then
        continue;
    end if;
    print g1, g0, h1, h0;
    print Ps;

    S<x,y,z> := CoordinateRing(X);
    PP1 := Curve(ProjectiveSpace(K, 1));

    den := (g2^2*h1 - g2*g1*h2 + h2^2)*y*z + (g2^2*h0 - g2*g0*h2)*z^2;
    a0 := (g2*h0 - g0*h2)*x^2 + ((g2^2*h0 - g2*g0*h2)*y^2 + (g2*g1*h0 - g2*g0*h1 - h2*h0)*y*z);

    if a0*den eq 0 then
        continue;
    end if;

    m := map< X -> PP1 | [a0, den] >;
    print Degree(m);

    for P in Ps[1..1] do
        minvP := Pullback(m, Place(m(X ! P)));
        Supp := Support(minvP);
        if #Supp eq 4 then
            print P;
            print Supp;
            for Q in Supp do
                seq := Eltseq(RepresentativePoint(Q));
                u := seq[1]; v := seq[2];

                den := (g2^2*h1 - g2*g1*h2 + h2^2)*v + g2^2*h0 - g2*g0*h2;
                a0 := (g2*h0 - g0*h2)/den*u^2 + ((g2^2*h0 - g2*g0*h2)*v^2 + (g2*g1*h0 - g2*g0*h1 - h2*h0)*v)/den;
                a1 := 0;
                b0 := (g2^2*h0 - g2*g0*h2)/den*u^3 + ((g2^3*h0 - g2^2*g0*h2)*v^2 + (g2^2*g1*h0 - g2*g1*g0*h2 - g2*h2*h0 + g0*h2^2)*v + g2^2*g0*h0 - g2*g0^2*h2)/den*u;
                b1 := b0/v;

                R<t> := PolynomialRing(K);
                a := t^2 + a1*t + a0;
                b := b1*t + b0;
                print "";
                print a;
                print b;
            end for;
            done := true;
        end if;
    end for;
end while;
