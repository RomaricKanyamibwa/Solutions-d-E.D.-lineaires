# -*- coding: utf-8 -*-
"""
Created on Tue Mar 14 14:44:25 2017
@author: HAKAM Sophia ,DJERRAB Mohamed, KANYAMIBWA Romaric
"""

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
from copy import copy

def isDFiniteFunction(D):
    """
    Verifie si D est une DFiniteFunction
    """
    return  isinstance(p,DFiniteFunction)
    
    
def calc_sum_func(L,CI,x):
    """
    -L est une liste fonctions L=[f1,f2,. . . . ,fn]
    -CI est une liste de nombres(Condition initiales au point x) CI=[g1(x0),g2(x0), . . . . . ,gn(x0)]
    -x is an x0 point at which we evaluate the functions in L
    Cette fonction calcule H(x0)=-(f1(x0)*g1(x0)+f2(x0)*g2(x0)+ . . . . . +fn(x0)*gn(x0))
    """
    if(len(L)<len(CI)+1):
        raise ValueError,"Incompatible length of L and CI .CI and L must have a length difference of 1"
    t=0
    for i in range(len(L)-1):
        if(isinstance( L[i], ( int, long,float,complex,Integer,Rational ) )):
            l=L[i]
        else:
            l=L[i](x)
        t+=CI[i]*l
    return -t

def calc_init_con(diff_eq,n):
    """
    -diff_eq est une variable de type DFiniteFunction 
    -n est un entier
    Cette function calcule les n premiers conditions initiales de diff_eq
    
    Exemple:
    
    sage: from ore_algebra import *;
    sage: from  DFiniteFunction import *;R.<x> = PolynomialRing(QQ); A.<Dx> = OreAlgebra(R);
    sage: diff_eq= Dx^2+16
    sage: cos4t=DFiniteFunction(diff_eq,[1,0])
    sage: calc_init_con(cos4t,5)
    [1, 0, -16, 0, 256, 0]
    
    """
    op=(diff_eq.annihilator().parent().gen())
    if(isinstance(diff_eq.annihilator(),Polynomial)):
        op=(diff_eq.annihilator().parent().gen())
        A = OreAlgebra(QQ[str(op)], 'D'+str(op))
        L=diff_eq.coefficients()
        x0=diff_eq.get_x0()
        CI=[diff_eq.coefficients()[0](x0)]
        d=copy(diff_eq.annihilator())
        order_d=0
        while(len(CI)-1<n):
            d=A(str())*d
            L=d.list()
            CI=CI+[calc_sum_func(L,CI,x0)]
        return CI
    if(not(isinstance(diff_eq,DFiniteFunction)) and not(isinstance(n,int))):
        raise TypeError,"Expected 2 aguments of type DFiniteFunction and int type"
    n=int(n)
    if(n<0):
        raise ValueError,"order is always a positive integer"
    length_IC=len(diff_eq.get_init_cond())
    if(length_IC>n):
        return diff_eq.get_init_cond()[:n+1]
    else:
        CI=diff_eq.get_init_cond()
        L=diff_eq.coefficients()
        x0=diff_eq.get_x0()
        CI=CI+[calc_sum_func(L,CI,x0)]
        d=copy(diff_eq.annihilator())
        order_d=d.order()
        while(d.order()!=n):
            d=op*d
            L=d.list()
            CI=CI+[calc_sum_func(L,CI,x0)]
        return CI

def PolyToDiff(P,n = 1,x=0):
    """
    P: est un polynome
    n: est l'ordre de l'equa diff à construire
    x: est le point x0 surlequel on definira les conditions initiales
    Cette fonction retourne la DFiniteFunction associé au polynome  P au point x

    Exemple:

    sage: P=3*x^4 - 6*x^3 + 5
    sage: print cos4t.PolyToDiff(P)
    (Dx - 12*x^3 + 18*x^2,[5])

    """
    op=P.parent().gen()
    if(isinstance(P,Polynomial)):
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
                break
        h=P
        ch = 'D'+str(op)+'^' + str(n)
        A = OreAlgebra(QQ[op],'D'+str(op))
        z = A(ch) - h
        return DFiniteFunction(z,L,x)
    else:
        raise TypeError,"A Polynomial function is expected as argument"

    
class DFiniteFunction(object):

    """Calcul formel sur des solutions d'équations différentielles linéaires
        -diff_eq est une equation differentielle de type 'ore_algebra.ore_operator_1_1.UnivariateDifferentialOperatorOverUnivariateRing'
        -init_cond est une liste de conditions initiales
        -et x0 (optionel) est le point sur lequel on definit les conditions initiales
        
        
    Exemple:
    
    sage: from ore_algebra import *;
    sage: from  DFiniteFunction import *;R.<x> = PolynomialRing(QQ); A.<Dx> = OreAlgebra(R);
    sage: diff_eq= Dx-4
    sage: exp4t=DFiniteFunction(diff_eq,[1])
    
     ou
     
    sage: exp4t=DFiniteFunction(diff_eq,[1],0)
        
    """
    
    def __init__(self,diff_eq,init_cond=[],x0=0):
        self.__diff_eq = diff_eq
        self.__x0=x0
        if(isinstance(diff_eq,UnivariateOreOperator)):
            if(len(init_cond)>=diff_eq.order()):#raise an error if diff_eq est une fonction
                self.__init_cond=init_cond
            else:
                raise ValueError,"not enough initial values."
        elif isinstance(diff_eq,Polynomial):
            self.__diff_eq = diff_eq
            self.__x0=x0
            if(init_cond!=[]):
                if diff_eq(x0)!=init_cond[0]:
                    raise ValueError,"Initial conditions incompatible with entered function"
            self.__init_cond=[]
        else:
            raise TypeError,"Incompatible type: expected diff_eq of Polynomial or UnivariateOreOperator type"

    def annihilator(self):
        """
        L'equation differentiel associé à self
        """
        return self.__diff_eq
    
    def get_x0(self):
        return self.__x0
   
    def get_init_cond(self):
        """
        Retourne la liste avec les conditions initiales
        """
        return self.__init_cond
        
    def order(self):
        """
        L'ordre de l'equation differentiel associé à self
        
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
        Retourne le degree du polynome de plus grand degree
        
        Exemple:
        sage: D=x*Dx+x^2
        sage: D=DFiniteFunction(D,[1])
        sage: D.degree()
        2
        """
        return self.__diff_eq.degree()

    def print_eq(self):
        """
        Fonction d'affichage de DFiniteFunction
        
        Exemple:
        sage: D=x*Dx+x^2
        sage: D=DFiniteFunction(D,[1])
        Dfinite equation:
        ('Initiale Conditions at x0=0:', [1])
        ('Equation:', x*Dx + x^2)
        """
        print ("Dfinite equation:")
        print ("Initiale Conditions at x0="+str(self.__x0)+":",self.__init_cond)
        print ("Equation:",self.__diff_eq)
        
    def __repr__(self):
        ch="("+str(self.__diff_eq)+","+str(self.__init_cond)+")"
        return str(ch)
        
    def __eq__(self,other):
        """
        Tests whether or not 2 functions are equal or not 
        """ 
        if self.__diff_eq==other.annihilator() and self.__init_cond==other.get_init_cond():
            return True
        length=min(len(self.__init_cond),len(other.get_init_cond()))
        if self.__init_cond[:length]!=other.get_init_cond()[:length]:
            return False
        temp_diff=self-other
        L=temp_diff.get_init_cond()
        zeroList=[0]*len(L)
        if((temp_diff.annihilator()==other.annihilator() or self.__diff_eq==temp_diff.annihilator()) and L==zeroList):
            return True
        elif calc_init_con(temp_diff,temp_diff.order()*2)==[0]*(temp_diff.order()*2):
            return True
        elif L!=zeroList:
            return False
        
    def __ne__(self,other):
        """
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
        while(i< n):
            newlist.append( -self.__init_cond[i])
            i += 1
        z = DFiniteFunction(z0,newlist,self.__x0)
        return z
        
    
    def __sub__(self,other):
        """Sustraction de 2 equa diff"""
        z=-other
        return self+z

    def __add__(self,other):
        """Addition de 2 equa diff"""
        
        if(isinstance( other, ( int, long,float,complex,Integer,Rational ) )): #or isinstance(other,Polynomial)):
            L=copy(self.__init_cond)
            if( not L):
                L=[other]
            else:
                L[0]=other+self.__init_cond[0]
            return DFiniteFunction(self.__diff_eq+other,L,self.__x0)
        
        if(isinstance(other,Polynomial)):
            pol_D=DFiniteFunction(other,[],self.__x0)
            return self+pol_D
        
        if(not(isinstance(self,DFiniteFunction))):
            raise TypeError,"Incompatible type:"+str(type(self))
            
        if(not(isinstance(other,DFiniteFunction))):
            raise TypeError,"Incompatible type:"+str(type(other))
            
        if(isinstance(self.__diff_eq,Polynomial)or isinstance(other.__diff_eq,Polynomial)):
            z0=self.__diff_eq+other.annihilator()
            if(isinstance(z0,Polynomial)):
                if(self.__x0!=other.get_x0()):
                    raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
                return DFiniteFunction(z0,[],self.__x0)
        else:
            z0=self.__diff_eq.lclm(other.annihilator())
        newlist =[]
        n=z0.order()
        L1=calc_init_con(self,n-1)
        L2=calc_init_con(other,n-1)
        i=0
        newlist = [L1[i] + L2[i] for i in range(n)]
        if(self.__x0!=other.get_x0()):
            raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
        z = DFiniteFunction(z0,newlist,self.__x0)
        return z


    def __mul__(self,other):
        """Multiplication de 2 equa diff"""
        if(isinstance(self.__diff_eq,Polynomial) or isinstance(other.__diff_eq,Polynomial)):
            z0=self.__diff_eq*other.annihilator()
            if(isinstance(z0,Polynomial)):
                if(self.__x0!=other.get_x0()):
                    raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
                return DFiniteFunction(z0,[],self.__x0)
        else:
            z0=self.__diff_eq.symmetric_product(other.annihilator())
        newlist =[]
        n=z0.order()
        L1=calc_init_con(self,n-1)
        L2=calc_init_con(other,n-1)
        i=0
        newlist = [L1[i] * L2[i] for i in range(n)]
        if(self.__x0!=other.get_x0()):
            raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
        z = DFiniteFunction(z0,newlist,self.__x0)
        return z
    
    def derivative(self):
        """
        Cette fonction calcule le DFiniteFunction associé à la derive self
        
        Exemple:
        sage: print p
            (1/64*x^2*Dx^3 + (-2*x^2 + x + 7)*Dx^2 + (-x^2 + x - 3/2)*Dx + 34/3*x^2 - 7,[0, 1, 1])
        sage: print p.derivative()
            (1/64*x^2*Dx^4 + (-2*x^2 + 33/32*x + 7)*Dx^3 + (-x^2 - 3*x - 1/2)*Dx^2 + (34/3*x^2 - 2*x - 6)*Dx + 68/3*x,[0, 1, 1, -11/2])
        """
        op=(self.__diff_eq.parent().gen())
        tmp_diff=self.__diff_eq
        tmp_IC=self.__init_cond
        tmp_diff=op*tmp_diff
        n=tmp_diff.order()
        tmp_IC=calc_init_con(self,n-1)
        return DFiniteFunction(tmp_diff,tmp_IC,self.__x0)
    
    def composition(self,g):
        """
        Fonction qui retourne la composition de diff_op avec f (fog)
        Pour l'instant la fonction retourne la composition que en forme d'une equation diff et pas comme une DFiniteFunction
        
        Exemple:
        sage: cos4t=DFiniteFunction(Dx^2+4,[1,0])
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
            print "P(x,g)=",P(x,g(x))
            if(P(x,g(x))==0):
                d=self.__diff_eq.annihilator_of_composition(g)
                #print "Composition:",d
                return d
            else:
                #print "The Result is not a Dfinite function"
                #raise NotImplementedError
                raise TypeError("The Result is not a Dfinite function")
            
        else:
            raise TypeError("A Polynomial or a Rational function is expected as argument")
        
    def power_series(self,order=6):
        """
        order: est un entier naturel qui represente l'ordre de developement de la serie entiere
        Cette fonction retourne le developpement en serie  de l'equation differentielle self
        
        Exemple:
        
        sage: cos4t.power_series(10)
        512/315*x^8 - 256/45*x^6 + 32/3*x^4 - 8*x^2 + 1
        """
        diff_eq=self.__diff_eq
        CI=calc_init_con(self,order-1)
        L=[0]*order
        if(self.__x0==0):
            L[0]=CI[0]
            f=1
            for i in range(1,order):
                f=f*i
                L[i]=CI[i]/f
        else:
            an=diff_eq.to_S(OreAlgebra(QQ["n"], "Sn")) #Suite de la serie entiere associé à l'equation differentielle 
            an_order=an.order()
            L=an.to_list(CI,order)
        K = FractionField(PolynomialRing(QQ,'x',order='negdeglex')) #utiliser pour faire le polynome P(x,g(x)) de la composition
        return K(L)
    

        
        