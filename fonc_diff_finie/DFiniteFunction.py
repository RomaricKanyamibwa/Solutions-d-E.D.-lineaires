# -*- coding: utf-8 -*-
"""
Created on Tue Mar 14 14:44:25 2017
@author: HAKAM Sophia, DJERRAB Mohamed, KANYAMIBWA Romaric

DFiniteFunction
================

Special classes for the implementation of DFiniteFunctions in SageMath with the use of the Ore_algebra module

"""

#############################################################################
#  Copyright (C) 2017                                                       #
#                                                                           #
#                                                                           #
#  Distributed under the terms of the GNU General Public License (GPL)      #
#  either version 3, or (at your option) any later version                  #
#                                                                           #
#  http://www.gnu.org/licenses/                                             #
#############################################################################

from __future__ import absolute_import


from sage.rings.integer_ring import ZZ
from ore_algebra.ore_operator import OreOperator, UnivariateOreOperator
from sage.rings.polynomial.polynomial_element import Polynomial
from sage.rings.fraction_field_element import FractionFieldElement #Espace de Fonction rationelle
from sage.rings.rational_field import QQ
from sage.calculus.functional import derivative
from sage.rings.fraction_field import FractionField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from ore_algebra.ore_algebra import OreAlgebra
from sage.rings.rational import Rational
from sage.rings.integer import Integer
from sage.arith.all import binomial
from sage.combinat.combinat import bell_polynomial
from sage.rings.power_series_ring import PowerSeriesRing
from copy import copy

def isDFiniteFunction(D):
    """
    Verifie si D est une DFiniteFunction
    """
    return  isinstance(D,DFiniteFunction)
    
    
def calc_sum_func(L,CI,x):
    """
    INPUT:
    -L est une liste de fonctions L=[f1,f2,. . . . ,fn]
    -CI est une liste de nombres(Condition initiales au point x) CI=[g1(x0),g2(x0), . . . . . ,gn(x0)]
    -x is an x0 point at which we evaluate the functions in L
    OUTPUT:
    Cette fonction calcule H(x0)=-(f1(x0)*g1(x0)+f2(x0)*g2(x0)+ . . . . . +fn(x0)*gn(x0))
    """
    if(len(L)<len(CI)+1):
        raise ValueError("Incompatible length of L and CI .CI and L must have a length difference of 1")
    t=0
    for i in range(len(L)-1):
        if(isinstance( L[i], ( int, long,float,complex,Integer,Rational ) )):
            l=L[i]
        else:
            l=L[i](x)
        t+=CI[i]*l
        
    if(not(isinstance( L[-1], ( int, long,float,complex,Integer,Rational ) ))):
        t=t/L[-1](x)
    else:
        t=t/L[-1]
    return -t

def calculate_initial_conditions(DFin_func,n,x=0):
    """
    -DFin_func est une variable de type DFiniteFunction ou un polynôme ou une fraction rationnelle
    -n est un entier
    -X (optionel) le point d'évaluation si DFinFunc est un polynôme
    Cette fonction calcule les n premières conditions initiales de diff_eq
    
    Exemple:
    
    sage: from ore_algebra import *;
    sage: from  DFiniteFunction import *;R.<x> = PolynomialRing(QQ); A.<Dx> = OreAlgebra(R);
    sage: diff_eq= Dx^2+16
    sage: cos4t=DFiniteFunction(diff_eq,[1,0])
    sage: calculate_initial_conditions(cos4t,5)
    [1, 0, -16, 0, 256, 0]
    
    """
    if(isinstance(DFin_func,Polynomial) or isinstance(DFin_func,FractionFieldElement)):
        if(isinstance(DFin_func,FractionFieldElement)):
            if(DFin_func.denominator()(x)==0):
                raise NotImplementedError("the function g is not defined at x0="+str(self.__x0))
        CI=[DFin_func(x)]
        P=copy(DFin_func)
        for i in range(n):
            P=P.derivative()
            if(isinstance(P, ( int, long,float,complex,Integer,Rational) )):
                CI=CI+[P]
            else:
                CI=CI+[P(x)]
        return CI
            
    
    op=(DFin_func.annihilator().parent().gen())
    if(not(isinstance(DFin_func,DFiniteFunction))):
        raise TypeError("Expected a DFiniteFunction or polynomial argument and not a "+str(type(DFin_func)))
    n=int(n)
    if(n<0 or not(isinstance(n,int))):
        raise ValueError("order n must always be a positive integer")
    length_IC=len(DFin_func.initial_conditions()[1])
    if(length_IC>n):
        return DFin_func.initial_conditions()[1][:n+1]
    else:
        CI=DFin_func.initial_conditions()[1]
        L=DFin_func.coefficients()
        x0=DFin_func.initial_conditions()[0]
        CI=CI+[calc_sum_func(L,CI,x0)]
        d=copy(DFin_func.annihilator())
        order_d=d.order()
        while(d.order()<n):
            d=op*d
            L=d.list()
            CI=CI+[calc_sum_func(L,CI,x0)]
        return CI

def PolyToDiff(Poly,order = 1,x=0):
    """
    Poly: est un polynôme
    order: est l'ordre de l'équa diff à construire
    x: est le point x0 surlequel on définira les conditions initiales
    Cette fonction retourne la DFiniteFunction associée au polynôme P au point x

    Exemple:

    sage: P=3*y^4 - 6*y^3 + 5
    sage: PolyToDiff(P)
    DFiniteFunction((3*y^4 - 6*y^3 + 5)*Dy - 12*y^3 + 18*y^2,[5])

    """
    P=copy(Poly)
    op=P.parent().gen()
    ch = 'D'+str(op)
    A = OreAlgebra(op.base_ring()[op],'D'+str(op))
    #if(isinstance(P, ( int, long,float,complex,Integer,Rational ) )):
        #print "Oper:",A(ch)
        #return DFiniteFunction(A(ch),[P],x
    if(isinstance(P,Polynomial) or isinstance(P,FractionFieldElement)):
        n=order
        h = copy(P)
        L = [0]*n
        for i in range(n):
            L[i] = P(x)
            tmp=P
            P = P.derivative()
            if(P==0):
                L=L[:i]
                n=i
                P=tmp
                if(n==0):
                    return DFiniteFunction(A(ch),[Poly],x)
                break
        h=P
        euclid=(Poly).quo_rem(h) # division euclidienne de Poly avec h
        SavePoly=euclid[0]+euclid[1]/(h)
        ch = 'D'+str(op)+'^' + str(n)
        z = SavePoly.denominator()*(SavePoly*A(ch) - 1)
        if(z.coefficients()):
            if(z.coefficients()[-1](x)==0):
                #raise ValueError("Forbiden value, x0="+str(x)+" is a singular point")
                x0=ZZ.random_element()
                while(z.coefficients()[-1](x0)==0):
                    x0=Poly.base_ring().random_element()
                P=copy(Poly)
                for i in range(n):
                    L[i] = P(x0)
                    P = P.derivative()
                print("Forbiden value, x0="+str(x)+" is a singular point . . . switching x0 point to "+str(x0))
                return DFiniteFunction(z,L,x0)
        return DFiniteFunction(z,L,x)
    else:
        raise TypeError("A Polynomial function is expected as argument")

def Leibniz_Product_rule(f,g,n):
    """
    Pour une question de lisibilité, on note Dx^n(f(x0)) la dérivée n_ieme de f au point x0
    Input:
    -f est une liste de valeurs de taille au moins n [f(x0),Dx(f(x0)),.....,Dx^n(f(x0))]
    -g est une liste de valeurs de taille au moins n [g(x0),Dx(g(x0)),.....,Dx^n(g(x0))]
    -n est un entier
    Output:
    -A la sortie, cette fonction renvoie le produit de Leibniz de la fonction Dx^n(f*g) au point x0
    """
    if(len(f)>n and len(g)>n):
        Leibniz_sum=0
        for k in range(n+1):
            #print("binomial(n+1,k)*f[n+1-k]*g[k]=",binomial(n,k)*f[n-k]*g[k])
            Leibniz_sum=Leibniz_sum+binomial(n,k)*f[n-k]*g[k]
        return Leibniz_sum
    else:
        raise TypeError("Incompatible list length,the list f and g must have at least n+1 elements")
        
def Faa_di_Bruno_formula(f,g,n):
    """
    Faà di Bruno's formula pour la dérivation de f(g(x))
    -f est une liste de valeurs de taille au moins n [f(x0),Dx(f(x0)),.....,Dx^n(f(x0))]
    -g est une liste de valeurs de taille au moins n [g(x0),Dx(g(x0)),.....,Dx^n(g(x0))]
    -n est un entier
    Output:
    -A la sortie, cette fonction renvoie Dx^n(f(g(x))) en x0 en utilisant la formule de Faà di Bruno
    """
    if(len(f)>=n and len(g)>=n):
        Faa_di_Bruno_sum=0
        for k in range(n):
            var_x=tuple(g[1:n-k+1])
            #print "x:",var_x
            #print "bell",bell_polynomial(n,k+1)
            Bell_pol=bell_polynomial(n,k+1)(var_x)
            #print Bell_pol
            Faa_di_Bruno_sum=Faa_di_Bruno_sum+f[k+1]*Bell_pol
        #print "Res:",Faa_di_Bruno_sum
        return Faa_di_Bruno_sum
    else:
        raise TypeError("Incompatible list length,the list f and g must have at least n elements")

    
class DFiniteFunction(object):

    """
        INPUT:
        Calcul formel sur des solutions d'équations différentielles linéaires
        -diff_eq est une équation différentielle de type 'ore_algebra.ore_operator_1_1.UnivariateDifferentialOperatorOverUnivariateRing'
        -initial_conditions est une liste de conditions initiales
        -et x0 (optionel) est le point sur lequel on définit les conditions initiales
        
        OUTPUT:
        -A DFiniteFunction
        
        
        
    Exemple:
    
    sage: from ore_algebra import *;
    sage: from  DFiniteFunction import *;R.<x> = PolynomialRing(QQ); A.<Dx> = OreAlgebra(R);
    sage: diff_eq= Dx-4
    sage: exp4t=DFiniteFunction(diff_eq,[1])
    
     ou
     
    sage: exp4t=DFiniteFunction(diff_eq,[1],0)
        
    """
    
    def __init__(self,diff_eq,initial_conditions=[],x0=0):#constructeur de la classe DFiniteFucntion
        self.__diff_eq = diff_eq
        self.__x0=x0
        #Avant de construire la DFiniteFunction on verifie que le coefficient dominant ne s'annule pas en x0
        if(diff_eq.coefficients()):
            if(isinstance(diff_eq.coefficients()[-1],Polynomial)):
                if(diff_eq.coefficients()[-1](x0)==0):
                    raise ValueError("Forbiden value, x0="+str(x0)+" is a singular point")
        if(isinstance(diff_eq,UnivariateOreOperator)):
            if(len(initial_conditions)>=diff_eq.order()):#on souleve une exception si les Condition initiales ne suffisent pas pour decrire la fonction
                self.__initial_conditions=initial_conditions
            else:
                raise ValueError("Not enough initial values.")
        else:
            raise TypeError("Incompatible type: expected a UnivariateOreOperator type")
            
    def toDFiniteFunction(self,func,x0=0):
        """
        INPUT:
        -func est une fonction de classe C infinie ou au moins une fonction de classe C 1
        
        OUTPUT:
        -cette méthode retourne la DFiniteFunction associée à func si elle existe
        
        (Pour l'instant, cette méthode ne marche que pour des polynômes mais dans une future
        implémentation, on peut essayer de tranformer d'autres fonction en DFiniteFunction comme les
        log(1+x),sinx,cosx,tanx,1/(1-x),. . .   qu'on sait qu'ils sont développable en série entière)
        """
        if isinstance(func,Polynomial):
            return PolyToDiff(func,1,x0)
        else:
            raise TypeError("Incompatible type: expected a Polynomial type")

    def annihilator(self):
        """
        L'opérateur différentiel associé à self
        """
        return self.__diff_eq
    
    def initial_conditions(self):
        """
        Retourne le couple (x0,ini) x0 est le point sur lequel les conditions initiales sont definies
        """
        return (self.__x0,self.__initial_conditions)
        
    def order(self):
        """
        L'ordre de l'équation différentielle associé à self
        
        Exemple:
        sage: diff_eq= Dx^7+16*x*Dx^4
        sage: D=DFiniteFunction(diff_eq,[1,0])
        sage: D.order()
        7
        """
        if(isinstance(self.__diff_eq,Polynomial)):
            return 0
        return self.__diff_eq.order()

    def degree(self):
        """
        Retourne le degré du polynôme de plus grand degré
        
        Exemple:
        sage: D=x*Dx+x^2
        sage: D=DFiniteFunction(D,[1])
        sage: D.degree()
        2
        """
        return self.__diff_eq.degree()

    def print_DFiniteFunction(self):
        """
        Fonction d'affichage de DFiniteFunction
        
        Exemple:
        sage: D=x*Dx+x^2
        sage: D=DFiniteFunction(D,[1])
        Dfinite equation:
        ('Initiale Conditions at x0=0:', [1])
        ('Equation:', x*Dx + x^2)
        """
        print ("D-Finite function:")
        print ("Initiale Conditions at x0="+str(self.__x0)+":",self.__initial_conditions)
        print ("Equation:",self.__diff_eq)
        
    def __repr__(self):
        ch="DFiniteFunction("+str(self.__diff_eq)+","+str(self.__initial_conditions)+",x0="+str(self.__x0)+")"
        return str(ch)
        
    def __eq__(self,other):
        """
        Tests whether or not 2 functions are equal or not 
        
        Exemple:
        sage: my_arctan = DFiniteFunction((z^2+1)*Dz^2 + 2*z*Dz, [0,1])
        sage: PolyToDiff(1/(z^2+1))
        DFiniteFunction((z^2 + 1)*Dz + 2*z,[1],x0=0)
        sage: PolyToDiff(1/(z^2+1))==my_arctan.derivative()
        True
        """
        if(self.__x0!=other.__x0):
            raise NotImplementedError("Cannot yet compare D-Finite Functions defined in different Points")
        if self.__diff_eq==other.annihilator() and self.__initial_conditions==other.initial_conditions()[1]:
            return True
        length=min(len(self.__initial_conditions),len(other.initial_conditions()[1]))
        if self.__initial_conditions[:length]!=other.initial_conditions()[1][:length]:
            return False
        temp_diff=self-other
        L=temp_diff.initial_conditions()[1]
        zeroList=[0]*len(L)
        if((temp_diff.annihilator()==other.annihilator() or self.__diff_eq==temp_diff.annihilator()) and L==zeroList):
            return True
        elif calculate_initial_conditions(temp_diff,temp_diff.order()*2)==[0]*(temp_diff.order()*2):
            return True
        elif L!=zeroList:
            return False
        
    def __ne__(self,other):
        """
        Test de différence de deux DFinteFunctions
        """
        return not(self==other)
    
    def coefficients(self):
        """
        This function returns a list with the coefficients of diff_eq
        -diff_eq est de type UnivariateOreOperator
        
        Exemple:
        sage: from ore_algebra import *;
        sage: from  DFiniteFunction import *;R.<x> = PolynomialRing(QQ); A.<Dx> = OreAlgebra(R);K=A.random_element(3);
        sage: p=DFiniteFunction(K,[0,1,1],0);
        sage: print p
        (1/64*x^2*Dx^3 + (-2*x^2 + x + 7)*Dx^2 + (-x^2 + x - 3/2)*Dx + 34/3*x^2 - 7,[0, 1, 1])
        sage: p.coefficients()
        [34/3*x^2 - 7, -x^2 + x - 3/2, -2*x^2 + x + 7, 1/64*x^2]
        """
        if(isinstance(self.__diff_eq,Polynomial)):
            return [self.__diff_eq]
        return self.__diff_eq.list()
    
    def __neg__(self):
        z0=-self.annihilator()
        newlist =[]
        n=self.order()
        i=0
        newlist = [-self.__initial_conditions[i] for i in range(n)]
        z = DFiniteFunction(z0,newlist,self.__x0)
        return z
        
    
    def __sub__(self,other):
        """Sustraction de 2 equa diff"""
        z=-other
        return self+z

    def __add__(self,other):
        """Addition de 2 equa diff"""
        if(isinstance( other, ( int, long,float,complex,Integer,Rational ) )):
            L=copy(self.__initial_conditions)
            L[0]=other+self.__initial_conditions[0]
            return DFiniteFunction(self.__diff_eq,L,self.__x0)
        
        if(isinstance(other,Polynomial)):
            pol_D=PolyToDiff(other,1,self.__x0)
            return self+pol_D

        if(not(isinstance(other,DFiniteFunction))):
            raise TypeError,"Incompatible type:"+str(type(other))
            
        if(self.__x0!=other.initial_conditions()[0]):
            raise ValueError("Incompatible initial condition, the initial conditions must be defined on the same point x0")
            
        else:
            z0=self.__diff_eq.lclm(other.annihilator())
        newlist =[]
        n=z0.order()
        L1=calculate_initial_conditions(self,n-1)
        L2=calculate_initial_conditions(other,n-1)
        i=0
        newlist = [L1[i] + L2[i] for i in range(n)]
        z = DFiniteFunction(z0,newlist,self.__x0)
        return z


    def __mul__(self,other):
        """Multiplication de 2 equa diff
        sage:cos4t=DFiniteFunction(Dy^2+16,[1,0])
        sage: cos4t*cos4t*cos4t
        DFiniteFunction(Dz^4 + 160*Dz^2 + 2304,[1, 0, -48, 0],x0=0)
        """
        if(isinstance( other, ( int, long,float,complex,Integer,Rational ) )):
            L=[other*self.__initial_conditions[i] for i in range(self.order())]
            return DFiniteFunction(self.__diff_eq,L,self.__x0)
        
        if(isinstance(other,Polynomial)):
            pol_D=PolyToDiff(other,1,self.__x0)
            return self*pol_D

        if(not(isinstance(other,DFiniteFunction))):
            raise TypeError,"Incompatible type:"+str(type(other))
            
        if(self.__x0!=other.initial_conditions()[0]):
            raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
        else:
            z0=self.__diff_eq.symmetric_product(other.annihilator())
        newlist =[]
        n=z0.order()
        L1=calculate_initial_conditions(self,n-1)
        L2=calculate_initial_conditions(other,n-1)
        i=0
        newlist = [Leibniz_Product_rule(L1[:i+1],L2[:i+1],i) for i in range(n)]
        z = DFiniteFunction(z0,newlist,self.__x0)
        return z
    
    def __pow__(self,n):
        """
        sage:cos4t=DFiniteFunction(Dy^2+16,[1,0])
        sage: cos4t^3
        DFiniteFunction(Dz^4 + 160*Dz^2 + 2304,[1, 0, -48, 0],x0=0)
        """
        res=self.__diff_eq.symmetric_power(n)
        order=res.order()
        Ring=self.__diff_eq.base_ring()
        CI=calculate_initial_conditions(self,order)
        L=[0]*order
        L[0]=CI[0]
        f=1
        for i in range(1,order):
            f=f*i
            L[i]=CI[i]/f
        power_series=Ring(L)
        power_series_n=power_series**n
        coeff_power_series_n=power_series_n.coefficients(sparse=False)
        Initial_conditions=[0]*order
        f=1
        Initial_conditions[0]=coeff_power_series_n[0]
        for i in range(1,order):
            f=f*i
            Initial_conditions[i]=coeff_power_series_n[i]*f
            
        return DFiniteFunction(self.__diff_eq.symmetric_power(n),Initial_conditions,self.__x0)
    
    def __call__(self,g):
        """
        Composition avec une fonction g (et, plus tard, évaluation d'une fonction)
        
        sage: my_exp(2*z)
        DFiniteFunction(Dz - 2,[1],x0=0)
        """
        if(isinstance(g,Polynomial) or isinstance(g,FractionFieldElement)):
            return self.composition(g)
        else:
            raise NotImplementedError# ici il faut faire l'evaluation de la fonction dans un point g
    
    def derivative(self):
        """
        Cette fonction calcule la dérivée d'une DFiniteFunction
        
        Exemple:
        sage: my_arctan=DFiniteFunction((z^2 + 1)*Dz^2 + 2*z*Dz,[0, 1],0)
        sage: my_arctan.derivative()
        DFiniteFunction((z^2 + 1)*Dz + 2*z,[1],x0=0)
        sage: my_arctan.derivative().annihilator()(arctan(z).derivative())
        0
        """
        op=(self.__diff_eq.parent().gen())
        tmp_diff=self.__diff_eq.annihilator_of_associate(op)
        tmp_IC=self.__initial_conditions
        n=tmp_diff.order()
        tmp_IC=calculate_initial_conditions(self,n)
        return DFiniteFunction(tmp_diff,tmp_IC[1:],self.__x0)
    
    def integral(self,y0=0):
        """
        INPUT:
        y0:  la valeur de l'intégrale de la fonction en x0
        
        OUTPUT:
        cette fonction calcule l'intégrale de la DFiniteFunction
        
        sage: my_log = DFiniteFunction(z*Dz^2+Dz, [0,1], x0=1)
        sage: my_log.integral()
        DFiniteFunction(z*Dz^3 + Dz^2,[0, 0, 1],x0=1) 
        sage: my_log.integral().annihilator()(log(z).integral(z))
        0
        
        RMQ: Dans cette fonction, la première condition initiale F(x0)=y0 serait presque toujours 0 parce que on ne connait pas explicitement la primitive de notre fonction
        """
        diff=self.__diff_eq.annihilator_of_integral()
        order=diff.order()
        Ring=self.__diff_eq.base_ring()
        IC=calculate_initial_conditions(self,order)
        L=[0]*order
        L[0]=IC[0]
        f=1#factoriel
        for i in range(1,order):
            f=f*i
            L[i]=IC[i]/f
        power_series=Ring(L)#generation de la serie entiere
        power_series_n=power_series.integral()#integration de la serie entiere
        coeff_power_series_n=power_series_n.coefficients(sparse=False)#extraction des conditions initiales 
        Initial_conditions=[0]*order
        f=1
        Initial_conditions[0]=y0
        for i in range(1,order):
            f=f*i
            Initial_conditions[i]=coeff_power_series_n[i]*f
        return DFiniteFunction(diff,Initial_conditions,self.__x0)
    
    def composition(self,g):
        """
        g est une fraction rationnelle ou un polynôme
        Fonction qui retourne la composition de diff_op avec f (f o g)
        Pour l'instant, la fonction retourne la composition uniquement sous la forme d'une équation diff et pas comme une DFiniteFunction
        
        Exemple:
        sage: cos4t=DFiniteFunction(Dx^2+16,[1,0])
        sage: cos4t.composition(x^2)
            ('Fraction Field', x^2)
            P(x,g)= 0
            Composition: x*Dx^2 - Dx + 64*x^3
            x*Dx^2 - Dx + 64*x^3
        """
        
        if(isinstance(g,Polynomial) or isinstance(g,FractionFieldElement)):
            #print("Fraction Field:",g)
            
            x, y = QQ['x','y'].gens()
            P=g(x)-y
            #print "P(x,g)=",P(x,g(x))
            if(P(x,g(x))==0):
                #print "Composition:",d
                if(isinstance(g,FractionFieldElement)):
                    if(g.denominator()(self.__x0)==0):
                         raise NotImplementedError("the function g is not defined at x0="+str(self.__x0)+" need to implement __call__ in order to treat this case")
                
                d=self.__diff_eq.annihilator_of_composition(g)
                if(g(self.__x0)==self.__x0):
                    n=d.order()-1
                    IC_f=calculate_initial_conditions(self,n)
                    IC_g=calculate_initial_conditions(g,n,self.__x0)
                    Initial_conditions=[self.__initial_conditions[0]]
                    if(n>=1):
                        Initial_conditions= Initial_conditions+[Faa_di_Bruno_formula(IC_f,IC_g,i+1) for i in range(n)]
                    #print "Order",n+1
                    #print "Init values:",Initial_conditions
                    return DFiniteFunction(d,Initial_conditions,self.__x0)
                
                tmp_Polynome=g-self.__x0# polynome P=g(x)-x0
                if(isinstance(tmp_Polynome,FractionFieldElement)):
                    tmp_Polynome=tmp_Polynome.numerator()
                    
                tmpList=tmp_Polynome.roots(self.__diff_eq.base_ring().base())#on cherche les points fixe de g tel que P=0 càd g(x1)=x0
                
                #print "Roots:",tmpList
                if(tmpList):
                    x0=tmpList[0][0]
                    n=d.order()-1
                    IC_f=calculate_initial_conditions(self,n)
                    IC_g=calculate_initial_conditions(g,n,x0)
                    Initial_conditions=[self.__initial_conditions[0]]
                    if(n>=1):
                        Initial_conditions= Initial_conditions+[Faa_di_Bruno_formula(IC_f,IC_g,i+1) for i in range(n)]
                    #print "Order",n+1
                    #print "Init values:",Initial_conditions
                    return DFiniteFunction(d,Initial_conditions,x0)# Dès qu'on trouve x1 on construit la definite function definit en x1 et pas en x0
                else:#pour faire cette partie de la composition il faut mettre en place une fonction call
                    #print "Roots:",tmpList
                    raise NotImplementedError("for an x1 other than the x0 of the initial values f(g(x)) is not implemented yet.")
            else:
                #print "The Result is not a Dfinite function"
                raise NotImplementedError("The Result is not a Dfinite function")
            
        else:
            raise TypeError("A Polynomial or a Rational function is expected as argument")
        
    def power_series(self,order=6):
        """
        order: est un entier naturel qui représente l'ordre du dévelopement de la série formelle
        Cette fonction retourne le developpement en série entière de l'équation différentielle en x0
        
        Exemple:
        
        sage: cos4t.power_series(10)
        1 - 8*z^2 + 32/3*z^4 - 256/45*z^6 + 512/315*z^8 + O(z^10)
        """
        diff_eq=self.__diff_eq
        Ring=diff_eq.base_ring()
        Ring_gen=diff_eq.base_ring().gen()
        CI=calculate_initial_conditions(self,order)
        L=[0]*order
        L[0]=CI[0]
        f=1
        for i in range(1,order):
            f=f*i
            L[i]=CI[i]/f
        if(self.__x0!=0):
            PowerSeries=Ring(L)
            PowerSeries=PowerSeries(Ring_gen-self.__x0)
            return PowerSeries
        #K = FractionField(PolynomialRing(QQ,str(op), order='neglex'))
        Power_ring=PowerSeriesRing(Ring,Ring_gen)
        return Power_ring(L).O(order)
    

        
        
