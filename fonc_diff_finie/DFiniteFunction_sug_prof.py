# -*- coding: utf-8 -*-
"""
Created on Tue Mar 14 14:44:25 2017
@author: HAKAM Sophia ,DJERRAB Mohamed, KANYAMIBWA Romaric
"""

# >>> Généralités :
#
# - Bug ?
#
# sage: my_arctan = dfin_op((x^2+1)*Dx^2 + 2*x*Dx, [0,1])
# sage: my_exp = dfin_op(Dx-1, [1])
# sage: ((my_exp + my_arctan)*my_exp).power_series()
# -17/60*x^5 - 41/24*x^4 - 5/3*x^3 + 1/2*x^2 + 2*x + 1
# sage: (my_exp*my_exp + my_arctan*my_exp).power_series()
# 41/120*x^5 + 1/2*x^4 + 3/2*x^3 + 3*x^2 + 3*x + 1
#
# - Je ne suis pas fan de la présentation de votre code. Vous pouvez
# regarder
#     https://www.python.org/dev/peps/pep-0008/
# pour une descriptions des conventions de présentation habituelles en
# Python, ou vous inspirer de celles utilisées dans le source de Sage.
# Après, ce n'est pas bien grave, et les conventions sont aussi faites
# pour être ignorées ;-)


# >>> On conseille en général d'éviter les "import *" dans du code de
# bibliothèque.

from ore_algebra import *
from sage.rings.integer_ring import ZZ
from sage.functions.other import *
from sage.all import *
from ore_algebra.ore_operator import OreOperator, UnivariateOreOperator
from sage.rings.polynomial.polynomial_element import Polynomial
from sage.rings.fraction_field_element import FractionFieldElement #Espace de Fonction rationelle
from sage.rings.rational_field import QQ
from sage.calculus.functional import derivative

# >>> Vous ne devriez pas avoir besoin de ça. Et actuellement, votre
# code a des problèmes avec les fonctions d'une variable autre que x.
# Par exemple :
#
# sage: Pols.<y> = QQ[]
# sage: Pols.<y> = PolynomialRing(QQ)
# sage: f = dfin_op(Dy^2 + y, [1, 2])
# sage: g = dfin_op(Dy + y, [1])
# sage: f + g
#
# Mieux vaut utiliser les parents des objets passés par l'utilisateur.
# Par exemple, dop.parent().gen() où dop est un opérateur différentiel
# renvoie la dérivation correspondante (Dx, Dy...), dop.base_ring()
# renvoie l'anneau de polynômes associé, etc.

K = FractionField(PolynomialRing(QQ, 'x')) #utiliser pour faire le polynome P(x,g(x)) de la composition
A = OreAlgebra(QQ['x'], 'Dx')


def calc_sum_func(L,CI,x):
    """
    -L is a list of functions L=[f1,f2,. . . . ,fn]
    -CI is a list of numbers (Initial conditions at x) CI=[g1(x0),g2(x0), . . . . . ,gn(x0)]
    -x is an x0 point at which we evaluate the functions in L
    Cette fonction calcule H(x0)=-(f1(x0)*g1(x0)+f2(x0)*g2(x0)+ . . . . . +fn(x0)*gn(x0))
    """
    if(len(L)<len(CI)+1):
        raise ValueError,"Incompatible length of L and CI .CI and L must have a length difference of 1"
    t=0
    for i in range(len(L)-1):
        if(isinstance( L[i], ( int, long,float,complex ) )):
            l=L[i]
        else:
            l=L[i](x)
        t+=CI[i]*l
    return -t

def calc_init_con(diff_eq,n):
    """
    -diff_eq est une variable de type dfin_op 
    -n est un entier
    Cette fonction calcule les n premières conditions initiales de diff_eq
    
    Exemple:
    
    sage: from ore_algebra import *;
    sage: from  dfin_op import *;R.<x> = PolynomialRing(QQ); A.<Dx> = OreAlgebra(R);
    sage: diff_eq= Dx^2+16
    sage: cos4t=dfin_op(diff_eq,[1,0])
    sage: calc_init_con(cos4t,5)
    [1, 0, -16, 0, 256, 0]
    
    """
    if(isinstance(diff_eq.get_diff_eq(),Polynomial)):
        
        L=diff_eq.coefficients()
        x0=diff_eq.get_x0()
        CI=[diff_eq.coefficients()[0](x0)]
        d=copy(diff_eq.get_diff_eq())
        order_d=0
        while(len(CI)-1<n):
            d=A('Dx')*d
            L=d.list()
            CI=CI+[calc_sum_func(L,CI,x0)]
        return CI
    if(not(isinstance(diff_eq,dfin_op)) and not(isinstance(n,int))):
        raise TypeError,"Expected 2 aguments of type dfin_op and int type"
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
        d=copy(diff_eq.get_diff_eq())
        order_d=d.order()
        while(d.order()!=n):
            d=A('Dx')*d
            L=d.list()
            CI=CI+[calc_sum_func(L,CI,x0)]
        return CI

# >>> La convention habituelle en Python est d'écrire les noms de
# classe en CamlCase (ici, je suggère DFiniteFunction).

class dfin_op(object):

    """Calcul formel sur des solutions d'équations
    différentielles linéaires
        -diff_eq est une equation differentielle de type 'ore_algebra.ore_operator_1_1.UnivariateDifferentialOperatorOverUnivariateRing'
        -init_cond est une liste de conditions initiales
        -et x0 (optionel) est le point sur lequel on definit les conditions initiales
        
        
    Exemple:
    
    sage: from ore_algebra import *;
    sage: from  dfin_op import *;R.<x> = PolynomialRing(QQ); A.<Dx> = OreAlgebra(R);
    sage: diff_eq= Dx-4
    sage: exp4t=dfin_op(diff_eq,[1])
    
     ou
     
    sage: exp4t=dfin_op(diff_eq,[1],0)
        
    """
    
    def __init__(self,diff_eq,init_cond=[],x0=0):
        self.__diff_eq = diff_eq
        self.__x0=x0
        # >>> Pas besoin de parenthèses autour de la condition.
        if((isinstance(diff_eq,UnivariateOreOperator))):
            # >>> Je ne comprends pas le commentaire.
            if(len(init_cond)>=diff_eq.order()):#raise an error if diff_eq est une fonction
                self.__init_cond=init_cond
            else:
                raise ValueError,"not enough initial values."
            # >>> Vérifiez aussi que le coefficient de tête ne
            # s'annule pas en x0.
        # >>> À quoi sert ce cas ? (Est-ce que ce serait parce que je
        # vous avais suggéré d'écrire une fonction qui transforme un
        # polynôme en fonction D-finie ? Dans ce cas, il y a eu un
        # malentendu : il faut que la fonction en question prenne un
        # polynôme p(x) et calcule un opérateur différentiel L tel que
        # L(p) = 0, ainsi que des conditions initiales.) En tout cas,
        # toutes les distinctions de cas de ce genre dans la suite
        # sont à virer...
        elif isinstance(diff_eq,Polynomial):
            self.__diff_eq = diff_eq
            self.__x0=x0
            if(init_cond!=[]):
                if diff_eq(x0)!=init_cond[0]:
                    raise ValueError,"Initial conditions incompatible with entered function"
            self.__init_cond=[]
        else:
            raise TypeError,"Incompatible type: expected diff_eq of Polynomial or UnivariateOreOperator type"

    # >>> Je renommerais cette méthode en annihilator(), par cohérence
    # avec ore_algebra.
    def get_diff_eq(self):
        """
        L'équation différentielle associée à self
        """
        return self.__diff_eq
    
    # >>> Peut-être regrouper les deux suivantes en une méthode
    # initial_values() qui renvoie (x0, ini).
    def get_x0(self):
        return self.__x0
   
    def get_init_cond(self):
        """
        Retourne la liste avec les conditions initiales
        """
        return self.__init_cond
        
    # >>> Les deux méthodes suivantes me semblent superflues.
    def order(self):
        """
        L'ordre de l'équation différentielle associée à self
        
        Exemple:
        sage: diff_eq= Dx^7+16*x*Dx^4
        sage: D=dfin_op(diff_eq,[1,0])
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
        sage: D=dfin_op(D,[1])
        sage: D.degree()
        2
        """
        return self.__diff_eq.degree()

    def print_eq(self):
        """
        Fonction d'affichage de dfin_op
        
        Exemple:
        sage: D=x*Dx+x^2
        sage: D=dfin_op(D,[1])
        Dfinite equation:
        ('Initiale Conditions at x0=0:', [1])
        ('Equation:', x*Dx + x^2)
        """
        print ("Dfinite equation:") # >>> "D-Finite function"
        print ("Initiale Conditions at x0="+str(self.__x0)+":",self.__init_cond)
        print ("Equation:",self.__diff_eq)
        
    # >>> Plutôt __repr__ que __str__, et renvoyez quelque chose du
    # genre DFiniteFunction(opérateur, ini).
    def __str__(self):
        ch="("+str(self.__diff_eq)+","+str(self.__init_cond)+")"
        return str(ch)
        
    def __eq__(self,other):
        """
        Tests whether or not 2 functions are equal or not 
        """ 
        # >>> Ce sont des objets de la même classe, vous pouvez
        # utiliser .__diff_eq() plutôt que get_diff_eq()
        if self.__diff_eq==other.get_diff_eq() and self.__init_cond==other.get_init_cond():
            return True
        length=min(len(self.__init_cond),len(other.get_init_cond()))
        if self.__init_cond[:length]!=other.get_init_cond()[:length]:
            return False
        temp_diff=self-other
        L=temp_diff.get_init_cond()
        zeroList=[0]*len(L)
        # >>> Je ne comprends pas la logique du code qui suit, ça m'a
        # l'air trop compliqué.
        if((temp_diff.get_diff_eq()==other.get_diff_eq() or self.__diff_eq==temp_diff.get_diff_eq()) and L==zeroList):
            return True
        elif calc_init_con(temp_diff,temp_diff.order()*2)==[0]*(temp_diff.order()*2):
            return True
        elif L!=zeroList:
            return False
        
    def __ne__(self,other):
        """
        """
        return not(self==other)
    
    # >>> Probablement superflu.
    def get_dfin_op(self):
        """
        Un tuple avec l'équation differentielle et les conditions initiales
        """
        return (self.__diff_eq,self.__init_cond)
    
    # >>> Probablement superflu. D'une façon générale, l'idée est
    # qu'un objet de cette classe doit représenter une *fonction*
    # solution d'une équa diff, pas l'équa diff elle-même.
    def coefficients(self):
        """
        This function returns a list with the coefficients of diff_eq
        -diff_eq est de type UnivariateOreOperator
        
        Exemple:
        sage: from ore_algebra import *;
        sage: from  dfin_op import *;R.<x> = PolynomialRing(QQ); A.<Dx> = OreAlgebra(R);K=A.random_element(3);
        sage: p=dfin_op(K,[0,1,1],0);
        sage: print p
        (1/64*x^2*Dx^3 + (-2*x^2 + x + 7)*Dx^2 + (-x^2 + x - 3/2)*Dx + 34/3*x^2 - 7,[0, 1, 1])
        sage: p.coefficients()
        [34/3*x^2 - 7, -x^2 + x - 3/2, -2*x^2 + x + 7, 1/64*x^2]
        """
        if(isinstance(self.__diff_eq,Polynomial)):
            return [self.__diff_eq]
        return self.__diff_eq.list()
    
    # >>> Pour éviter la duplication de code, mieux vaudrait définir
    # __neg__ (le moins unaire), et implémenter __sub__ via __neg__ et
    # __add__
    def __sub__(self,other):
        """Sustraction de 2 equa diff"""
        if(isinstance(self.__diff_eq,Polynomial) or isinstance(other.__diff_eq,Polynomial)):
            z0=self.__diff_eq-other.get_diff_eq()
            if(isinstance(z0,Polynomial)):
                if(self.__x0!=other.get_x0()):
                    raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
                return dfin_op(z0,[],self.__x0)
        else:
            z1=-other.get_diff_eq()
            z0=self.__diff_eq.lclm(z1)
        newlist =[]
        n=z0.order()
        L1=calc_init_con(self,n-1)
        L2=calc_init_con(other,n-1)
        i=0
        while(i< n):
            newlist.append(L1[i] - L2[i])
            i += 1
        # >>> Plutôt à remonter en début de fonction
        if(self.__x0!=other.get_x0()):
            raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
        z = dfin_op(z0,newlist,self.__x0)
        return z

    def __add__(self,other):
        """Addition de 2 equa diff"""
        if(isinstance(self.__diff_eq,Polynomial)or isinstance(other.__diff_eq,Polynomial)):
            z0=self.__diff_eq+other.get_diff_eq()
            if(isinstance(z0,Polynomial)):
                if(self.__x0!=other.get_x0()):
                    raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
                return dfin_op(z0,[],self.__x0)
        else:
            z0=self.__diff_eq.lclm(other.get_diff_eq())
        newlist =[]
        n=z0.order()
        L1=calc_init_con(self,n-1)
        L2=calc_init_con(other,n-1)
        # >>> Plus élégant :
        # newlist = [L1[i] - L2[i] for i in range(n)]
        # ou même :
        # newlist = [a - b for a, b in zip(L1, L2)]
        i=0
        while(i< n):
            newlist.append(L1[i] + L2[i])
            i += 1
        if(self.__x0!=other.get_x0()):
            raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
        z = dfin_op(z0,newlist,self.__x0)
        return z

    # >>> Vous pourriez aussi implémenter __pow__ dans le cas
    # (fonction D-finie)^entier.
    def __mul__(self,other):
        """Multiplication de 2 equa diff"""
        if(isinstance(self.__diff_eq,Polynomial) or isinstance(other.__diff_eq,Polynomial)):
            z0=self.__diff_eq*other.get_diff_eq()
            if(isinstance(z0,Polynomial)):
                if(self.__x0!=other.get_x0()):
                    raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
                return dfin_op(z0,[],self.__x0)
        else:
            z0=self.__diff_eq.symmetric_product(other.get_diff_eq())
        newlist =[]
        n=z0.order()
        L1=calc_init_con(self,n-1)
        L2=calc_init_con(other,n-1)
        i=0
        while(i< n):
            newlist.append(L1[i] * L2[i])
            i += 1
        if(self.__x0!=other.get_x0()):
            raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
        z = dfin_op(z0,newlist,self.__x0)
        return z
    
    # >>> Renommer en derivative()
    def get_derivative(self):
        """
        Cette fonction calcule le dfin_op associé à la dérivée self
        
        Exemple:
        sage: print p
            (1/64*x^2*Dx^3 + (-2*x^2 + x + 7)*Dx^2 + (-x^2 + x - 3/2)*Dx + 34/3*x^2 - 7,[0, 1, 1])
        sage: print p.get_derivative()
            (1/64*x^2*Dx^4 + (-2*x^2 + 33/32*x + 7)*Dx^3 + (-x^2 - 3*x - 1/2)*Dx^2 + (34/3*x^2 - 2*x - 6)*Dx + 68/3*x,[0, 1, 1, -11/2])
        """
        tmp_diff=self.__diff_eq
        tmp_IC=self.__init_cond
        tmp_diff=A('Dx')*tmp_diff
        n=tmp_diff.order()
        tmp_IC=calc_init_con(self,n-1)
        return dfin_op(tmp_diff,tmp_IC,self.__x0)
    
    def composition(self,g):
        """
        Fonction qui retourne la composition de diff_op avec f (fog)
        Pour l'instant, la fonction retourne la composition qu'en forme d'une équation différentielle et non comme un dfin_op
        
        Exemple:
        sage: cos4t=dfin_op(Dx^2+4,[1,0])
        sage: cos4t.composition(x^2)
            ('Fraction Field', x^2)
            P(x,g)= 0
            Composition: x*Dx^2 - Dx + 64*x^3
            x*Dx^2 - Dx + 64*x^3
        """
        
        if(isinstance(g,Polynomial) or isinstance(g,FractionFieldElement)):
            print("Fraction Field",g)
            x, y = QQ['x','y'].gens()
            P=g(x)-y
            print "P(x,g)=",P(x,g)
            if(P(x,g)==0):
                d=self.__diff_eq.annihilator_of_composition(g)
                print "Composition:",d
            else:
                # >>> Plutôt raise NotImplementedError
                print "The Result is not a Dfinite function"
            return d
            
        else:
            # >>> Plutôt raise TypeError(...) que , ... en Python
            # moderne
            raise TypeError,"A Polynomial or a Rational function is expected as argument"
            
    
    # >>> Superflu
    def coeff_power_series(self,order=10):
        """
        Les coefficients de la serie formelle associée à self
        
        Exemple:
        
        sage: cos4t.coeff_power_series()
        [1, 0, -8, 0, 32/3, 0, -256/45, 0, 512/315, 0]
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
            return L
        else:
            an=diff_eq.to_S(OreAlgebra(QQ["n"], "Sn")) #Suite de la serie entiere associé à l'equation differentielle 
            an_order=an.order()
            L=an.to_list(CI,order)
            return L
        
    def power_series(self,order=6):
        """
        order: est un entier naturel qui représente l'ordre de développement de la serie entiere
        Cette fonction retourne le developpement en serie  de l'equation differentielle self
        
        Exemple:
        
        sage: cos4t.power_series(10)
        512/315*x^8 - 256/45*x^6 + 32/3*x^4 - 8*x^2 + 1
        """
        L=self.coeff_power_series(order)
        
        return K(L)
    
    # >>> À sortir de la classe. Et ça n'a pas l'air de marcher :
    #
    # sage: foo = my_exp.PolyToDiff(x^2+1)
    # sage: foo.get_diff_eq()
    # Dx - 2*x
    # sage: zop = foo.get_diff_eq()
    # sage: zop(x^2+1)
    def PolyToDiff(self,P,n = 1,x = 0):
        """
        P: est un polynôme
        n: est l'ordre de l'equa diff à construire
        x: est le point x0 sur lequel on définira les conditions initiales
        Cette fonction retourne la dfin_op associée au polynome P au point x
        
        Exemple:
        
        sage: P=3*x^4 - 6*x^3 + 5
        sage: print cos4t.PolyToDiff(P)
        (Dx - 12*x^3 + 18*x^2,[5])

        """
        if(isinstance(P,Polynomial)):
            h = copy(P) # >>> Copie superflue.
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
            ch = 'Dx^' + str(n)
            z = A(ch) - h
            return dfin_op(z,L,x)
        else:
            raise TypeError,"A Polynomial function is expected as argument"


        
        
