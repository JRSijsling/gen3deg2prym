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

K<u,v> := FunctionField(X);
x := u; y := v; z := 1;
den := (g2^2*h1 - g2*g1*h2 + h2^2)*y*z + (g2^2*h0 - g2*g0*h2)*z^2;
a0 := (g2*h0 - g0*h2)*x^2 + ((g2^2*h0 - g2*g0*h2)*y^2 + (g2*g1*h0 - g2*g0*h1 - h2*h0)*y*z);

D := Divisor(a0/den);
print Support(Divisor(a0));
print Support(Divisor(den));
print Support(D);

