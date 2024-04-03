-- -*- coding: utf-8 -*-
newPackage(
    "DivisorIntersections",
    Version => "0.1",
    Date => "Never",
    Authors => {
	{Name => "Alexander Zenkovich", Email => "alexander.zenkovich@ens.psl.eu", HomePage => "https://www.youtube.com/watch?v=dQw4w9WgXcQ"}},
    Headline => "Divisor Intersection numbers",
    Keywords => {"Documentation"},
    DebuggingMode => false
    )

export {
    "numberOfPoints", 
}

loadPackage("Divisor", Reload=>true)
loadPackage("PrimaryDecomposition", Reload=>true)



countMonomialsBelow = l -> ( -- TODO: smarter point-counting method
    if ((length (l#0)) == 1) then min flatten l else (
    maxLastCoord := max apply(l, x -> last x);
    res := 0;
    for i from 1 to maxLastCoord do (
        lCur := select(l, x -> (last x) < i);
        a := countMonomialsBelow(apply(lCur, x -> drop(x,-1)));
        res = res + a
    );
    res)
)


numberOfPoints = I -> if isHomogeneous I then numberOfPointsProj I else numberOfPointsAff I

numberOfPointsProj = I -> (
    degree I
)
 
numberOfPointsAff = I -> (
    J := (flattenRing I)#0;
    leadExps := apply((entries leadTerm J)#0, x -> (exponents x)#0);
    countMonomialsBelow leadExps
)

intersectWithIdealInGP = (D, IE) -> (
    sum(apply(gbs D,
        gbDcomp -> (numberOfPoints(ideal(gbDcomp) + IE) * coefficient(gbDcomp, D))
    ))
)

isInGeneralPositionWithPrime = (D, IEcomp) -> (
    any(gbs D, gbDcomp -> ideal(gbDcomp) == IEcomp)
)

putIntoGeneralPositionWithPrimeAff = (D, IEcomp) -> (
    c := coefficient(IEcomp, D);
    if (c == 0) then D else
    isPrincipalGenerator = f -> (
        prims := primaryDecomposition ideal(f);  
        any(prims, x -> (x == IEcomp))
    )
    gensE := (entries gens IEcomp)#0;
    gensPrincipal := select(gensE, isPrincipalGenerator);
    assert(length gensPrincipal > 0);
    D - c * divisor(f)  
)

putIntoGeneralPositionWithPrimeProj = (D, IEcomp) -> (
    c := coefficient(IEcomp, D);
    if (c == 0) then D else
    isPrincipalGenerator = f -> (
        prims := primaryDecomposition ideal(f);  
        any(prims, x -> (saturate(x) == IEcomp))
    )
    gensE := (entries gens IEcomp)#0;
    gensPrincipal := select(gensE, isPrincipalGenerator);
    x := select(gens ring IEcomp, f -> (f % IEcomp) != 0);
    assert(length gensPrincipal > 0);
    D - c * (divisor(f) - (degree(f)#0) * divisor(x))
)

putIntoGeneralPositionWithPrime = (D, IEcomp) -> (
    if isHomogeneous(IEcomp) 
    then putIntoGeneralPositionWithPrimeProj(D, IEcomp) 
    else putIntoGeneralPositionWithPrimeAff(D, IEcomp)
)

intersectionNumber = (D, E) -> (
    Dt := trim D;
    Et := trim E;
    sum(apply(gbs Et,
        gbEcomp -> 
        IEcomp := ideal(gbEcomp);
        c := coefficient(IEcomp, Et);
        Dgp := putIntoGeneralPositionWithPrime(Dt, IEcomp);
        intIdx := intersectWithIdealInGP(Dgp, IEcomp);
        intIdx * c
    ))
)

beginDocumentation()

doc ///
///

TEST /// --check #1
assert (countMonomialsBelow {{2}, {3}, {1}, {4}} == 1)
assert (countMonomialsBelow {{4,0}, {1,3}, {2,2}, {3,1}, {0,4}} == 10)
///

TEST /// --check #2
R = QQ[x,y,z]
I = ideal(x^2 - 2, y^3 - x, z^5 - y)
assert (numberOfPointsAff I == 30)

R = QQ[x,y]
S = R / ideal(y - x^2)
I = ideal(y + x^2)
assert (numberOfPointsAff I == 2)
///
end--