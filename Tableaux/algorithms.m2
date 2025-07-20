
maxSSYT = method(TypicalValue => SkewTableau)
maxSSYT (Partition,Partition) := (lam,mu) -> (
    tempT := skewTableau(lam,mu);
    (lam,mu) = skewShapePadded tempT;

    entryList := for entryIndex from 0 to sum toList lam - sum toList mu - 1 list (
        (i,j) := indexToPosition(entryIndex,tempT);
        theCol := tempT_j;
        theColAbove := theCol_(toList(0..i));
        #(delete(null,theColAbove))
        );

    skewTableau(lam,mu,entryList)
    )

minSSYT = method(TypicalValue => SkewTableau)
minSSYT (Partition,Partition,ZZ) := (lam,mu,maxEntry) -> (
    tempT := skewTableau(lam,mu);
    (lam,mu) = skewShapePadded tempT;
    
    entryList := for entryIndex from 0 to sum toList lam - sum toList mu - 1 list (
        (i,j) := indexToPosition(entryIndex,tempT);
        theCol := tempT_j;
        theColBelow := theCol_(toList((i+1)..(#theCol-1)));
        maxEntry - #(delete(null,theColBelow))
        );

    skewTableau(lam,mu,entryList)
    )

addOneSSYT = method(TypicalValue => SkewTableau)
addOneSSYT (SkewTableau,Sequence,SkewTableau) := (T,thePosition,minSSYT) -> (
    if T_thePosition >= minSSYT_thePosition then return null;
    
    (lam,mu) := skewShapePadded T;
    (rowIndex,colIndex) := thePosition;

    if (rowIndex < 0) or (rowIndex >= #lam) then error "index out of range";
    if (colIndex < mu#rowIndex) or (colIndex >= lam#rowIndex) then error "index out of range";

    entryList := new MutableList from entries T;

    for currRowIndex from rowIndex to #T_colIndex-1 do (
        for currColIndex from colIndex to lam#currRowIndex-1 do (
            theIndex := positionToIndex((currRowIndex,currColIndex),T);
            
            currBox := entryList#theIndex;
            
            isBoxLeft := currColIndex > mu#currRowIndex;
            leftBox := if isBoxLeft then (
                leftIndex := positionToIndex((currRowIndex,currColIndex-1),T);
                entryList#leftIndex
                ) else (
                0
                );
            
            isBoxAbove := currRowIndex > 1 and currColIndex >= mu#(currRowIndex-1) and currColIndex < lam#(currRowIndex-1);
            aboveBox := if isBoxAbove then (
                aboveIndex := positionToIndex((currRowIndex-1,currColIndex),T);
                entryList#aboveIndex
                ) else (
                0
                );
            
            if thePosition == (currRowIndex,currColIndex) or currBox < leftBox or currBox <= aboveBox then (
                entryList#theIndex += 1;
                );
            );
        );

    skewTableau(lam,mu,toList entryList)
    )

allSSYT = method(TypicalValue => List)
allSSYT (Partition,Partition,ZZ) := (lam,mu,maxEntry) -> (
    (lam,mu) = skewShapePadded(lam,mu);
    (lamList,muList) := (toList lam, toList mu);

    if rsort lamList != lamList or rsort muList != muList then error "expected partitions to be weakly decreasing";
    
    if any(0..(#lam-1), i -> mu#i > lam#i) then return Bag {};

    T := skewTableau(lam,mu);

    if #lam == 0 then return Bag {skewTableau(new Partition from {})};
    if any(colRange T,i -> #colEntries(i,T) > maxEntry) then return Bag {};
    --if all(0..(#lam-1), i -> lam#i == mu#i) then return Bag {skewTableau(lam,mu)};

    maxT := maxSSYT(lam,mu);
    minT := minSSYT(lam,mu,maxEntry);

    recurse := (theIndex,T) -> (
        newT := addOneSSYT(T,indexToPosition(theIndex,T),minT);
        
        if newT =!= null then flatten ({newT} | for i from 1 to -theIndex list recurse(-i,newT))
        );

    --ans := {maxT} | flatten for theIndex from 1 to size T list recurse(-theIndex,maxT);
    ans := {maxT} | flatten parallelApply(1..(size T), theIndex -> recurse(-theIndex,maxT));

    Bag delete(null,ans)
    )
allSSYT (Partition,Partition) := (lam,mu) -> (
    (lam,mu) = skewShapePadded(lam,mu);
    maxEntry := #lam;
    
    allSSYT(lam,mu,maxEntry)
    )
allSSYT (Partition,ZZ) := (lam,maxEntry) -> (
    mu := new Partition from {0};
    
    allSSYT(lam,mu,maxEntry)
    )
allSSYT Partition := lam -> (
    mu := new Partition from {0};
    (lam,mu) = skewShapePadded(lam,mu);
    maxEntry := #lam;
    
    allSSYT(lam,mu,maxEntry)
    )

allRowWeakTableaux = method(TypicalValue => List)
allRowWeakTableaux (Partition,Partition,ZZ) := (lam,mu,maxEntry) -> (
    (lam,mu) = skewShapePadded(lam,mu);

    if any(0..(#lam-1), i -> mu#i > lam#i) then return Bag {};

    rowRST := for i from 0 to #lam-1 list (
        allSSYT(new Partition from {lam#i}, new Partition from {mu#i}, maxEntry)
        );

    seqOfRows := toList rowRST#0;
    for i from 1 to #rowRST-1 do (
        seqOfRows = seqOfRows ** (toList rowRST#i);
        );
    
    Bag for theSeq in seqOfRows/deepSplice list verticalConcatenate toList sequence theSeq
    )
allRowWeakTableaux (Partition,Partition) := (lam,mu) -> (
    (lam,mu) = skewShapePadded(lam,mu);
    maxEntry := #lam;

    allRowWeakTableaux(lam,mu,maxEntry)
    )
allRowWeakTableaux (Partition,ZZ) := (lam,maxEntry) -> (
    mu := new Partition from {0};

    allRowWeakTableaux(lam,mu,maxEntry)
    )
allRowWeakTableaux Partition := lam -> (
    mu := new Partition from {0};
    (lam,mu) = skewShapePadded(lam,mu);
    maxEntry := #lam;
    
    allRowWeakTableaux(lam,mu,maxEntry)
    )
allRowWeakTableaux (SkewTableau,ZZ) := (T,maxEntry) -> (
    (lam,mu) := skewShapePadded T;
    
    allRowWeakTableaux(lam,mu,maxEntry)
    )
allRowWeakTableaux SkewTableau := T -> (
    allRowWeakTableaux skewShapePadded T
    )

allJacobiTrudiShapes = method(TypicalValue => List)
allJacobiTrudiShapes (Partition,Partition) := (lam,mu) -> (
    (lam,mu) = skewShapePadded(lam,mu);

    indexProdList := for thePerm in permutations(#lam) list (
        for i from 0 to #lam-1 list (
            j := thePerm#i;
            (lam#i+j+1,mu#j+i+1)
            )
        );
    
    for theProd in indexProdList list (
        verticalConcatenate for theShape in theProd list skewTableau(new Partition from {theShape#0},new Partition from {theShape#1})
        )
    )
allJacobiTrudiShapes Partition := lam -> allJacobiTrudiShapes(lam,new Partition from {})

allJacobiTrudiTableaux = method(TypicalValue => List)
allJacobiTrudiTableaux (Partition,Partition,ZZ) := (lam,mu,N) -> Bag flatten for theT in allJacobiTrudiShapes(lam,mu) list toList allRowWeakTableaux(theT,N)
allJacobiTrudiTableaux (Partition,Partition) := (lam,mu) -> allJacobiTrudiTableaux(lam,mu,#lam)
allJacobiTrudiTableaux Partition := lam -> allJacobiTrudiTableaux(lam,new Partition from {},#lam)
