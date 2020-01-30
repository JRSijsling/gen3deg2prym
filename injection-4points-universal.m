/***
 *  Proves that X --> Jac (Y) is injective
 *
 *  Copyright (C) 2019
 *            Jeroen Sijsling  (jeroen.sijsling@uni-ulm.de)
 *
 *  See LICENSE.txt for license details.
 */

F := Rationals();
K<g1,g0,h1,h0> := RationalFunctionField(F, 4);
g2 := 1; h2 := 1;

S<x,y,z> := PolynomialRing(K, 3);
G := y^2 + g1*y*z + g0*z^2;
H := y^2 + h1*y*z + h0*z^2;
F := x^4 + x^2*G + y*z*H;

X := PlaneCurve(F);
KU<u,v> := FunctionField(X);
X := ChangeRing(X, KU);
P := X ! [u, v, 1];

S<x,y,z> := CoordinateRing(X);
PP1 := Curve(ProjectiveSpace(BaseRing(X), 1));

den := (g2^2*h1 - g2*g1*h2 + h2^2)*y*z + (g2^2*h0 - g2*g0*h2)*z^2;
a0 := (g2*h0 - g0*h2)*x^2 + ((g2^2*h0 - g2*g0*h2)*y^2 + (g2*g1*h0 - g2*g0*h1 - h2*h0)*y*z);
b0 := (g2^2*h0 - g2*g0*h2)*x^3 + ((g2^3*h0 - g2^2*g0*h2)*y^2 + (g2^2*g1*h0 - g2*g1*g0*h2 - g2*h2*h0 + g0*h2^2)*y*z + (g2^2*g0*h0 - g2*g0^2*h2)*z^2)*x;

assert a0*den ne 0;
m1 := map< X -> PP1 | [a0, den] >;
m2 := map< X -> PP1 | [b0, den*z] >;
m1invP := Pullback(m1, Place(m1(P)));

Supp := Support(m1invP);
for Q in Supp do
    print Pushforward(m2, Q);
end for;
