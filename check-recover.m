/***
 *  Gives a single example of a projection
 *
 *  Copyright (C) 2019
 *            Jeroen Sijsling  (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

function BinaryQuarticInvariants(bq);

R<x> := Parent(bq);

a := Coefficient(bq, 4);
b := Coefficient(bq, 3);
c := Coefficient(bq, 2);
d := Coefficient(bq, 1);
e := Coefficient(bq, 0);

I := 12*a*e - 3*b*d + c^2;
J := 72*a*c*e + 9*b*c*d - 27*a*d^2 - 27*e*b^2 - 2*c^3;
Delta := 4*I^3 - J^2;
a := -I/3; b := -J/27;
j := 1728*(a^3/(a^3 + 27/4*b^2));

return j, I, J;

end function;


print "";
print "Check whether degree-2 cover indeed yields X --> E with relevant Prym.";

R<x,y,z> := PolynomialRing(Rationals(), 3);
S<t> := PolynomialRing(Rationals());
h := hom< R -> S | [t,1,0] >;

F := -147*x^4 + 33600*x^3*y - 47754*x^2*y^2 - 30714566613792449844251611322833165170806*x^2*z^2 + 302400*x*y^3 + 41186925172831693192625629999750980519500*x*y*z^2 - 11907*y^4 - 33597651375890668367735405422815733807171*y^2*z^2 + 270548428880815869019024278307589533734724908495598267479905812799696505328*z^4;
G0 := F;

f0 := &+[ MonomialCoefficient(G0, z^4)*t^0 ];
f2 := &+[ MonomialCoefficient(G0, x^i*y^(2-i)*z^2)*t^i : i in [0..2] ];
f4 := &+[ MonomialCoefficient(G0, x^i*y^(4-i))*t^i : i in [0..4] ];
j := BinaryQuarticInvariants(S ! (-(f2/(2*f0))^2 + (f4/f0)));
p1 := (t - 1)*t*(t + 1)*(t + 2);
j0 := BinaryQuarticInvariants(p1);

print "";
print "Check genus 1 invariant:";
print j;
print j0;

K := SplittingField(h(G0));
H0 := ChangeRing(G0, K);
R<x,y,z> := Parent(H0);
S<t> := PolynomialRing(K);
H0 /:= MonomialCoefficient(H0, z^4);

print "";
rts := [ rt[1] : rt in Factorization(ChangeRing(h(H0), K)) ];
for pair in [ [1,2,3,4], [1,3,2,4], [1,4,2,3] ] do
    hX := -&+[ MonomialCoefficient(H0, x^i*y^(2-i)*z^2)*t^i : i in [0..2] ];
    fX := MonomialCoefficient(H0, x^4)*rts[pair[1]]*rts[pair[2]];
    gX := rts[pair[3]]*rts[pair[4]];

    //print "Check that factorization works:";
    //print H0 eq (z^4 - y^2*Evaluate(hX, x/y)*z^2 + y^4*Evaluate(fX*gX, x/y));

    f2 := Coefficient(fX, 2); f1 := Coefficient(fX, 1); f0 := Coefficient(fX, 0);
    g2 := Coefficient(gX, 2); g1 := Coefficient(gX, 1); g0 := Coefficient(gX, 0);
    h2 := Coefficient(hX, 2); h1 := Coefficient(hX, 1); h0 := Coefficient(hX, 0);

    A := Matrix([ [ f2, f1, f0 ], [ h2, h1, h0 ], [ g2, g1, g0 ] ]);
    B := A^(-1);

    a1 := B[1,1]; b1 := B[1,2]; c1 := B[1,3];
    a2 := B[2,1]; b2 := B[2,2]; c2 := B[2,3];
    a3 := B[3,1]; b3 := B[3,2]; c3 := B[3,3];

    a := a1 + 2*a2*t + a3*t^2;
    b := b1 + 2*b2*t + b3*t^2;
    c := c1 + 2*c2*t + c3*t^2;

    f0 := 2*b*(b^2 - a*c);
    p0 := f0/LeadingCoefficient(f0);
    J := IgusaInvariants(p0);

    print "Candidate Igusa invariants:";
    print WPSNormalize([2,4,6,8,10], J);
    // [ 1, 709/23762, 1216/1295029, 27495/2258530576, 153/61544958196 ]
end for;

print "";
print "Correct Igusa invariants:";
p2 := (t + 3)*(t + 1)*t*(t - 1)*(t - 3)*(t - 4);
J := IgusaInvariants(p2);
print WPSNormalize([2,4,6,8,10], J);
