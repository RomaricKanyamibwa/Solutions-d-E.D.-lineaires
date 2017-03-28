print("Starting test script")
from ore_algebra import *;
from  dfin_op import *;R.<x> = PolynomialRing(ZZ); A.<Dx> = OreAlgebra(R);K=A.random_element(3);
p=dfin_op(K,[0,1,1]);
print('-------------------------------------------------------------------------')
K=A.random_element(2);s=dfin_op(K,[0,1]);
print("Randomly generated functions s and p:")
print('-------------------------------------------------------------------------')
p.print_eq();
s.print_eq();
print('-------------------------------------------------------------------------')
print("Sum of s and p")
print('-------------------------------------------------------------------------')
Z=s+p;
Z.print_eq()
print('-------------------------------------------------------------------------')
print("Test of dfin_function:")
print('-------------------------------------------------------------------------')
from dfin_functions import *
n=2
calc_init_con(s,n)
calc_init_con(s,n+3)
print('-------------------------------------------------------------------------')
