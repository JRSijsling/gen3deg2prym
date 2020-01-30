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
//K := F;
//g1 := 4; g0 := 5; h1 := 3; h0 := -4;

S<x,y,z> := PolynomialRing(K, 3);
G := y^2 + g1*y*z + g0*z^2;
H := y^2 + h1*y*z + h0*z^2;
F := x^4 + x^2*G + y*z*H;
X := PlaneCurve(F);

S<x,y,z> := CoordinateRing(X);
PP3 := ProjectiveSpace(K, 3);

S<x,y,z> := PolynomialRing(K, 3);
den := (g2^2*h1 - g2*g1*h2 + h2^2)*y + (g2^2*h0 - g2*g0*h2)*z;
a0 := (g2*h0 - g0*h2)/den*x^2 + ((g2^2*h0 - g2*g0*h2)*y^2 + (g2*g1*h0 - g2*g0*h1 - h2*h0)*y*z)/den;
b0 := (g2^2*h0 - g2*g0*h2)/den*x^3 + ((g2^3*h0 - g2^2*g0*h2)*y^2 + (g2^2*g1*h0 - g2*g1*g0*h2 - g2*h2*h0 + g0*h2^2)*y*z + (g2^2*g0*h0 - g2*g0^2*h2)*z^2)/den*x;
b1 := b0/y;

deqs := [a0*z, b0, b1*z, z^2];
deqs := [ S ! (deq*(y*den)) : deq in deqs ];

m := map< X -> PP3 | deqs >;
I := Image(m);
m := map< X -> Curve(I) | deqs >;
print Degree(m);

