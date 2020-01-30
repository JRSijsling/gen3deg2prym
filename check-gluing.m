/***
 *  Gives a single example of a projection
 *
 *  Copyright (C) 2019
 *            Jeroen Sijsling  (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

function PrymPols(F);

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
B := A^(-1);

a1 := B[1,1]; b1 := B[1,2]; c1 := B[1,3];
a2 := B[2,1]; b2 := B[2,2]; c2 := B[2,3];
a3 := B[3,1]; b3 := B[3,2]; c3 := B[3,3];

a := a1 + 2*a2*t + a3*t^2;
b := b1 + 2*b2*t + b3*t^2;
c := c1 + 2*c2*t + c3*t^2;

f := b*(b^2 - a*c);
fell := h^2 - 4*fg;
return f, fell;

end function;


while true do
    B := 5; D := [-5..5];
    K := RationalsExtra();
    S<x,y,z> := PolynomialRing(K, 3);

    repeat
        F := Random(D)*x^4 + &+[ Random(D)*mon : mon in [y^2, y*z, z^2] ]*x^2 + &+[ Random(D)*mon : mon in [y^2, y*z, z^2] ]*y*z;
        I := DixmierOhnoInvariants(F);
    until I[#I] ne 0;
    g, h := PrymPols(F);
    //g /:= LeadingCoefficient(g);

    print "";
    print "Genus 3:";
    print F;
    print "Genus 2:";
    print g;
    print "Genus 1:";
    print h;

    X3 := PlaneCurve(F);
    X2 := HyperellipticCurve(g);
    X1 := HyperellipticCurve(h);

    P3 := PeriodMatrix(X3);
    P2 := PeriodMatrix(X2);
    P1 := PeriodMatrix(X1);

    GeoHomRep := GeometricHomomorphismRepresentation(P3, P2, K);

    print "";
    print "Representation on differentials (no normalization, det (A) present):";
    print GeoHomRep[1][1];
    R := GeoHomRep[1][2];
    E3 := StandardSymplecticMatrix(3);

    print "";
    print "Degree if this would be a morphism:";
    print R*E3*Transpose(R);

    GeoHomRep := GeometricHomomorphismRepresentationCC(P3, P1);
    h := GeoHomRep[1];
    K := Ker0(h, P3, P1);

    GeoHomRep := GeometricHomomorphismRepresentationCC(K, P2);
    print "";
    print "Degree of map from Prym variety to genus 2 Jacobian:";
    print Determinant(GeoHomRep[1][2]);

    break;
end while;

Q3 := DiagonalJoin(P1, P2);
GeoHomRep := GeometricHomomorphismRepresentationCC(P3, Q3);
Rs := [ tup[2] : tup in GeoHomRep ];
R3 := Rs[1] + Rs[2];
E3 := StandardSymplecticMatrix(3);

print "";
print "Check whether RR-construction yields 2-gluing:";
print "Check diagonal join of standard matrices:";
print InducedPolarization(E3, R3);
