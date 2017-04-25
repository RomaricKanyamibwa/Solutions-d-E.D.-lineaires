K = FractionField(PolynomialRing(QQ, 'x'))
PolQ=K.random_element()
k=dfin_op(Dx-1,[1])
k.get_diff_eq().annihilator_of_composition(x*x*x)
Dx - 3*x^2
isinstance(PolQ,type(k))
type(PolQ)
Pol=R.random_element()
Pol
type(Pol)
p.composition(PolQ)

p.composition(x^2-5*x+1)