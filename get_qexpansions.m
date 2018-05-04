Qx<x>:=PolynomialRing(Rationals());

function get_character(f,eps_data) // returns the character eps attached to f

    K:=Parent(Coefficient(f,0));
    N:=eps_data[1];
    gens:=eps_data[2];
    G:=DirichletGroup(N,K);
    // In some levels > 1000 the construction of this group can take an infinity of time!
    
    for eps in Elements(G) do // just look for the character with correct values on the generators
        if [eps(gens[i][1]) eq gens[i][2]: i in [1 .. #gens]] eq [true: i in [1 .. #gens]] then
            return eps;
        end if;
    end for;
end function;


function eisenstein_series_weight_one(eps,K,qprec) // returns E_1(1,eps) modulo q^qprec

    Sq<q>:=PowerSeriesRing(K,qprec); // K is the codomain of the character
    
    M:=Conductor(eps);
    eps_prim:=AssociatedPrimitiveCharacter(eps);
    
    E0:=(-1/M)*&+[j*eps_prim(j): j in [0 .. M-1]];
    
    // E:=(E0/2) + &+[&+[eps(n):n in Divisors(m)]*q^m: m in [1 .. qprec - 1]];
    
    E:=(E0/2) + &+[&+[eps_prim(n):n in Divisors(m)]*q^m: m in [1 .. qprec - 1]]; 
        
    return E;

end function;

function write_in_basis(g,B) // writes a form g in terms of a basis B for the space in which it lies
    
    K:=Parent(Coefficient(B[1],0));
    g_vec:=[K!0: j in [1 .. #B]];
	for j:=1 to #B do
		Bj_leadingpos:=Valuation(B[j]);
		Bj_leadingcoeff:=Coefficient(B[j],Bj_leadingpos);
		g_vec[j]:=Coefficient(g,Bj_leadingpos)/Bj_leadingcoeff;
		g:=g - g_vec[j]*B[j];
	end for;

    assert g eq 0; // check g in space spanned by basis to given precision
    
    return g_vec; // returns a list expressing g in this basis

end function;


function extend_qexpansion(f,eps_data,qprec) // returns the q-expansion of the weight one form f to precision q^qprec

    eps:=get_character(f,eps_data); // construct the Dirichlet character of f
    K:=Parent(Coefficient(f,0));
    
    E_epsinv:=eisenstein_series_weight_one(eps^-1,K,qprec); // compute the weight one eisenstein series E_1(1,eps^-1)
    
    g:=f*E_epsinv; 
    // multiplying by the weight one eisenstein series gives a weight 2 form g, known to the smaller precision
    
    N:=eps_data[1];
    B:=Basis(CuspForms(N,2)); // find a basis for the space in which g lies
    B_K_qprec:=[Parent(E_epsinv)!PowerSeries(b,qprec): b in B]; // find the basis elements to higher precision
    
    B_K:=[Parent(f)!b: b in B_K_qprec];
    g_vec:=write_in_basis(g,B_K); // find the coefficients expressing g in this basis
    
    g_qprec:=&+[g_vec[i]*B_K_qprec[i]: i in [1 .. #B]]; // now recover g to higher precision
    
    f_qprec:=g_qprec*E_epsinv^-1; // dividing by the weight one Eisenstein series gives f to higher precision
    
    return f_qprec;

end function;
