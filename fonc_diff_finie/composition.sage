K = FractionField(PolynomialRing(QQ, 'y'))
PolQ=K.random_element()
k=DFiniteFunction(Dy-1,[1])
k.get_diff_eq().annihilator_of_composition(y^3)
Dy - 3*y^2
isinstance(PolQ,type(k))
type(PolQ)
Pol=R.random_element()
Pol
type(Pol)
p.composition(PolQ)

p.composition(y^2-5*y+1)