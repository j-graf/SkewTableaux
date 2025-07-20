

YngTableau = new Type of SkewTableau

yngTableau = method(TypicalValue => YngTableau)
yngTableau (Partition,List) := (lam,theList) -> (
    mu := new Partition from {};
    (lam',mu') := skewShapePadded(lam,mu);
    numBoxesNeeded := sum for i from 0 to #lam'-1 list max(lam'#i-mu'#i,mu'#i-lam'#i);
    
    if (numBoxesNeeded != #theList) then error "partition sizes do not match with the length of the list";
    if any(theList, theElt -> theElt === null) then error "filling must not contain null entries";

    new YngTableau from {
        "outerShape" => lam,
        "innerShape" => mu,
        values => theList
        }
    )
yngTableau Partition := lam -> (
    numBoxesNeeded := sum for i from 0 to #lam-1 list max(lam#i,-lam#i);
    
    yngTableau(lam, toList(numBoxesNeeded:""))
    )

skewTableau YngTableau := T -> new SkewTableau from T

shape = method(TypicalValue => Partition)
shape YngTableau := T -> (
    (lam,mu) := skewShape T;

    lam
    )

