/***
 *  Gives a single example of a projection
 *
 *  Copyright (C) 2019
 *            Jeroen Sijsling  (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

SetVerbose("EndoCheck", 0);

function PrymPol(F);

S<x,y,z> := Parent(F);
R<t> := PolynomialRing(BaseRing(S));

a := MonomialCoefficient(F, x^4);
b := MonomialCoefficient(F, x^2*y^2)*t^2 + MonomialCoefficient(F, x^2*y*z)*t + MonomialCoefficient(F, x^2*z^2);
c := MonomialCoefficient(F, y^4)*t^4 + MonomialCoefficient(F, y^3*z)*t^3 + MonomialCoefficient(F, y^2*z^2)*t^2 + MonomialCoefficient(F, y*z^3)*t + MonomialCoefficient(F, z^4);

h := -b/a;
fg := c/a;
f := t;
g := R ! (fg / f);

f2 := Coefficient(f, 2); f1 := Coefficient(f, 1); f0 := Coefficient(f, 0);
g2 := Coefficient(g, 2); g1 := Coefficient(g, 1); g0 := Coefficient(g, 0);
h2 := Coefficient(h, 2); h1 := Coefficient(h, 1); h0 := Coefficient(h, 0);

A := Matrix([ [ f2, f1, f0 ], [ h2, h1, h0 ], [ g2, g1, g0 ] ]);
if Determinant(A) eq 0 then
    return false, 0;
end if;
B := A^(-1);

a1 := B[1,1]; b1 := B[1,2]; c1 := B[1,3];
a2 := B[2,1]; b2 := B[2,2]; c2 := B[2,3];
a3 := B[3,1]; b3 := B[3,2]; c3 := B[3,3];

a := a1 + 2*a2*t + a3*t^2;
b := b1 + 2*b2*t + b3*t^2;
c := c1 + 2*c2*t + c3*t^2;

f := Determinant(A)^2*b*(b^2 - a*c);
return true, f;

end function;


L := [ ];
while true do
    B := 2; D := [-B..B];
    K := RationalsExtra();
    S<x,y,z> := PolynomialRing(K, 3);

    repeat
        G := &+[ Random(D)*mon : mon in [y^2, y*z, z^2] ];
        H := &+[ Random(D)*mon : mon in [y^2, y*z, z^2] ];;
        seqG := [ MonomialCoefficient(G, mon) : mon in [y^2, y*z, z^2] ];
        seqH := [ MonomialCoefficient(H, mon) : mon in [y^2, y*z, z^2] ];
        F := x^4 + x^2*G + y*z*H;
        I := DixmierOhnoInvariants(F);
    until I[#I] ne 0;

    test1, g := PrymPol(F);
    if test1 then
        test2, rt := IsSquare(Evaluate(g, 0));
        if test2 and (rt ne 0) then
            entry := [ seqG, seqH, [0, rt] ];
            if not entry in L then
                X := PlaneCurve(F);
                P0 := X ! [ 0, 0, 1 ];
                Y := HyperellipticCurve(g);
                Q0 := Y ! [ 0, rt, 1 ];
                T := Matrix(K, [[ 0, 0, -1], [0, 1, 0]]);

                time test, fs := CantorFromMatrixAmbientSplit(X, P0, Y, Q0, T);
                fs := [ X`KU ! f : f in fs ];
                ceqs := Y`cantor_eqs;
                assert &and[ Evaluate(ceq, fs) eq 0 : ceq in ceqs ];

                Y := BaseExtend(Y, X`KU);
                R<x> := PolynomialRing(BaseRing(Y));
                J := Jacobian(Y);

                a := x^2 + fs[1]*x + fs[2];
                b := fs[3]*x + fs[4];
                div1 := J ! [a, b];

                Q0 := Y ! [0, rt, 1];
                Q0m := Y ! [0, -rt, 1];
                div0 := Q0 - Q0m;

                print "";
                print "Quartic form:";
                print F;
                print "";
                print "Genus 2 curve:";
                print g;
                print Factorization(g);

                print "";
                print "Map to Jacobian induced by:";
                D := div1 - div0;
                print D;

                f := X`DEs[1];
                R<v> := RationalFunctionField(K);
                S<u> := PolynomialRing(R);
                f := Evaluate(f, [ u, v ]);
                LQ<u> := FieldOfFractions(quo< S | f >);

                h := hom< X`KU -> LQ | [ u, v ] >;
                seq := Eltseq(D);
                pols := Coefficients(seq[1]) cat Coefficients(seq[2]);
                pols := [ h(pol) : pol in pols ];

                g2, g1, g0 := Explode(seqG);
                h2, h1, h0 := Explode(seqH);

                den := (g2^2*h1 - g2*g1*h2 + h2^2)*v + g2^2*h0 - g2*g0*h2;
                a0 := (g2*h0 - g0*h2)/den*u^2 + ((g2^2*h0 - g2*g0*h2)*v^2 + (g2*g1*h0 - g2*g0*h1 - h2*h0)*v)/den;
                a1 := K ! 0;
                b0 := (g2^2*h0 - g2*g0*h2)/den*u^3 + ((g2^3*h0 - g2^2*g0*h2)*v^2 + (g2^2*g1*h0 - g2*g1*g0*h2 - g2*h2*h0 + g0*h2^2)*v + g2^2*g0*h0 - g2*g0^2*h2)/den*u;
                b1 := (g2^2*h0 - g2*g0*h2)/(den*v)*u^3 + ((g2^3*h0 - g2^2*g0*h2)*v^2 + (g2^2*g1*h0 - g2*g1*g0*h2 - g2*h2*h0 + g0*h2^2)*v + g2^2*g0*h0 - g2*g0^2*h2)/(den*v)*u;

                print "Coefficients:";
                print pols;
                assert pols eq [ a0, a1, 1, b0, b1 ];
            end if;
        end if;
    end if;
end while;

//x^4 - x^2*y^2 + x^2*y*z - 3*x^2*z^2 - y^3*z + 5*y*z^3
//x^4 - 4*x^2*y^2 - 2*x^2*y*z - 3*x^2*z^2 + 4*y^3*z + y^2*z^2 + 4*y*z^3
//x^4 - 3*x^2*y*z + 4*x^2*z^2 + 3*y^3*z - 4*y^2*z^2 - y*z^3
//x^4 + x^2*y*z - 2*x^2*z^2 - 2*y^3*z - 3*y^2*z^2 + 3*y*z^3
