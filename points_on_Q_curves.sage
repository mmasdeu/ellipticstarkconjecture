# # Sembla que un bon candidat per a començar és una f tingui caràcter trivial (quan hi ha caràcter sembla que la fórmula incorpora una suma de gauss, d'entrada està bé considerar un cas on no hi sigui)
# # De les Q-corbes que hi ha a QuerTable.pdf n'he trobat tres que tenen caracter trivial i que satisfan la hipòtesi de Heegner per a un cos K amb h(K) = 1 (suposo que volem d'entrada els punts de Heegner el més senzills possibles, i per tant amb K de nombre de classes 1):
# # N = 363, K = Q(-2)
# # N = 387, K = Q(-2)

# Exemple N = 363
F.<g> = QuadraticField(-11) # cos de definicio de la corba
K.<r>=QuadraticField(-2) # cos quadratic imaginari
c4 = 1/2*(-75*g-121) # c4 i c6 donats per en Quer
c6 = -90*g + 14414
E_non_minimal = EllipticCurve([-27*c4,-54*c6]) # conductor 33*OF; aquesta corba es la que dona en Quer, pero resulta que es molt millor (a l'hora de trobar punts algebraics amb magma) utilitzar el model minimal que defineixo mes avall

_.<x> =PolynomialRing(QQ)
KF.<s> = NumberField(x^4+26*x^2+81) # aixo es KF (composicio de K i F), construit directament a partir del seu polinomi minim; ho faig aixi perque aqui he fet alguns calculs amb magma i aquest es el generador que ell utitliza
_.<x> =PolynomialRing(KF)
# aquest es el model minimal de la nostra E, construit directament com a corba sobre KF
E = EllipticCurve([1/36*(-s^3 - 35*s - 18),1/36*(-s^3 - 35*s + 54), 0,1/18*(-s^3 - 35*s + 18),1/36*(-s^3 - 35*s - 90)])
gg = (x^2+11).roots()[0][0]
assert E.is_isogenous(EllipticCurve([-27*1/2*(-75*gg-121),-54*(-90*gg + 1441)]))
# these are, according to Magma, the generators of the mordell-weil group of E(KF)
P1 = E.point([1/36*(s^3 + 35*s + 54),-3])
P2 = E.point([1/36*(s^3 + 35*s - 18), 0])

# Exemple N = 387
F.<g> = QuadraticField(-3)
K.<r> = QuadraticField(-2)
c4 = 576*g + 288
c6 = 18144*g - 13176
Enm = EllipticCurve([-27*c4,-54*c6])
_.<x> =PolynomialRing(QQ)
KF.<s> = NumberField(x^4 + 10*x^2 + 1)
_.<x> =PolynomialRing(KF)
g = (x^2 + 3).roots()[1][0]
E = EllipticCurve([ 0, 6, 9, 9*g - 3, -3*g - 27 ]) # minimal model
assert E.is_isogenous(EllipticCurve([-27*(576*g + 288),-54*(18144*g - 13176)]))
P1 = E.point([1 , 1/4*(-3*s^3 - 33*s - 10)]) # torsio (ordre 3)
P2 = E.point([1/8*(-s^3 - 11*s - 18) , 1/8*(12*s^3 + 9*s^2 + 108*s + 9)]) # ordre infinit
P3 = E.point([1/2*(-2*s^3 - 22*s - 7),1/8*(-20*s^3 - 15*s^2 - 180*s - 111)])


# Ds = [-1, -2, -3, -7, -11, -19, -43, -67, -163]
# good_Ds = []
# for D in Ds:
#     if (kronecker_symbol(D,13) == 1 or kronecker_symbol(D,13) == 0) and kronecker_symbol(D,2) == 1:
#         good_Ds.append(D)
