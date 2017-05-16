# calcula gamma·tau, donde gamma es una matrix 2x2
def act(gamma,tau):
	a,b,c,d=gamma[0][0],gamma[0][1],gamma[1][0],gamma[1][1]
	return (a*tau+b)/(c*tau+d)

def find_good_D(N):
    good_Ds = []
    Ds=[-7, -11, -19, -43, -67, -163,-1,-2,-3]
    ps=N.factor()
    for D in Ds:
        K=QuadraticField(D)
        if all([kronecker_symbol(D,p[0])==1 for p in ps]) and gcd(D,N)==1:
            good_Ds.append(D)
    return good_Ds

def compute_embedding_alt(w,N):
	f=w.minpoly()
	if f.degree()!=2 or f.discriminant() >-1 or not w.is_integral():
		print 'Error: w no genera un cuadratico imaginario'
		raise RuntimeError
	M_aux=matrix(QQ,2,2,[0,-f[0],1,-f[1]])
	assert M_aux.minpoly()==f
	#esta matriz nos da un embedding de K en M_2(Z). Para calcular un embedding en M_2(N) tenemos que conjugar por una matriz de determinante N. Todas ellas son (salvo conjugacion en SL_2(Z)) de la forma [a,b,0,d] con ad=N,d>0 y b<d.
	#lo siguiente solo esta garantizado que funcione si N es primo
	for a in N.divisors():
		d=N/a
		for b in range(0,d):
			W=Matrix(QQ,2,2,[a,b,0,d])
			M=W*M_aux*W^-1
			if ((M[0][0]).is_integral() and (M[1][0]).is_integral() and (M[0][1]).is_integral() and (M[1][1]).is_integral()):
				
				return M
	#si no hemos encontrado el embedding es que no existe. Recordemos que el embedding solo existe si (D/p)=+1 para todo p|N			
	print 'Embedding no encontrado. Has comprovado que legendre_symbol(D,p) sea 1 para todo p|N?'
	return -1

def fixed_point(gamma):
	a,b,c,d=gamma[0][0],gamma[0][1],gamma[1][0],gamma[1][1]
	tau=((a-d)+((d-a)^2+4*b*c).sqrt())/(2*c)
	tau0=((a-d)+(RR((d-a)^2+4*b*c)).sqrt())/(2*c)
	return tau, tau0

def compute_heegner_point(f,tau,emb,num_digitos):
	# f=E.modular_form()
	z=0
	n=1
	exp_partial=1.0
	while exp_partial.abs()>10**(-num_digitos):
		an=emb(f.coefficients([n])[0])
		exp_partial=exp(2*pi*I*n*tau)
		z+=(an/n)*exp_partial
		n+=1
	print 'Hemos sumado hasta n=',n
	return z

prec=400
num_digits = 300
RR=RealField(prec)
CC=ComplexField(prec)
I=CC.gen()
pi=RR(pi)

# Exemple N = 29
N = 29
F.<g> = QuadraticField(29)
c4 = 1/2*(15*g+79)
c6 = 70*g + 369
E = EllipticCurve([-27*c4,-54*c6])
chi = kronecker_character(29)
f = Newforms(chi, 2, names = 'a')[0]
Qf = f.coefficients([2])[0].parent()
emb0, emb1 = Qf.embeddings(CC)
Ds = find_good_D(N) # D = -7
D = -7
K.<rD>=QuadraticField(D)
if D%4==1:
	w=(rD+1)/2
else:
	w=rD
M=compute_embedding_alt(w,N)
tau,tau0=fixed_point(M)
# print 'El embedding optimal es w-->M'
# print 'M='
# print M
# print 'El punto fijo es tau0=', tau0
z0=compute_heegner_point(f, tau0, emb0, num_digits)
z1=compute_heegner_point(f, tau0, emb1, num_digits)
psev = emb1(f.coefficients([29])[0])/RR(29).sqrt()
z = 1/(1+psev)*(z0 + psev*z1)
# print 'z=',z
#calculamos el periodo de E
Lambda=E.period_lattice(F.embeddings(CC)[0])
# este es el punto en E(CC) que corresponde a z por la aplicacion de Weierstrass C/Lambda -->E(CC)
P=Lambda.elliptic_exponential(z)
# print "Una aproximación al punto de Heegner es P=",P

x,y=P[0],P[1]

#esta funcion devuelve un polinomio de grado 2 cuya raiz aproxima x hasta num_digitos
pol_x_coord=algdep(x,2,num_digits-5)
print "la coordenada x se puede aproximar por una raíz del polinomio",pol_x_coord


print 'comprovamos que x_coord vive en K'
_.<y> = PolynomialRing(F)
KF.<gKF> = NumberField(y^2 - D)
KF.<gKF> = KF.absolute_field()
try: 
	KK.<x_coord>=NumberField(pol_x_coord.monic())
	#nos miramos la coordenada x como un punto de K
	x=KK.embeddings(KF)[0](x_coord)
	print 'la coordenada x encontrada es',x
except:
	print '!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!'
	print 'Error, la coordenada x del punto calculado no vive en KF'
	print '!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!'

#comprovamos que efectivamente es la coordenada x de un punto de K
EKF=E.base_extend(F.embeddings(KF)[0])
try:	
	P_K=EKF.lift_x(KF.automorphisms()[0](x))
	print 'El punto de Heegner calculado es',P_K
        print 'Tiene orden', P_K.order()
except ValueError:
	print 'Error, el punto calculado no se corresponde con un punto de la curva'
# 175*x^2 - 6714*x - 31068
