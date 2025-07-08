newPackage(
    "SkewTableaux",
    Version => "0.1",
    Date => "July 8, 2025",
    Authors => {
	{Name => "John Graf", Email => "grafjohnr@gmail.com", HomePage => "https://j-graf.github.io/"}},
    Headline => "a package for constructing skew tableaux",
    Keywords => {"Combinatorics"},
    DebuggingMode => false
    )

export {"SkewTableau", "skewTableau",
        "shape", "shape0", "reducedShape", "rowEntries", "colEntries", "isSkew", "indexToPosition", "positionToIndex",
        "allSSYT"}

--needsPackage "SpechtModule"

SkewTableau = new Type of HashTable
skewTableau = method(TypicalValue => SkewTableau)
skewTableau (Partition,Partition,List) := (lam,mu,theList)->(
    if (sum toList lam - sum toList mu != #theList) then error "partition sizes do not match with the length of the list";
    if (rsort toList lam != toList lam or rsort toList mu != toList mu) then error "partitions must be weakly decreasing";
    if any(lam, thePart -> thePart < 0) or any(mu, thePart -> thePart < 0) then error "partitions must have non-negative parts";
    if any(theList, theElt -> theElt === null) then error "filling must not contain null entries";
    
    newLam := new Partition from delete(0,toList lam);
    newMu := delete(0,toList mu);
    if #newMu > #newLam then error "mu must be contained in lam";
    newMu = new Partition from newMu|(toList((#newLam-#newMu):0));
    if any(toList(0..(#newMu-1)),i -> newMu#i > newLam#i) then error "mu must be contained in lam";
    
    new SkewTableau from {
        "outerPartition" => newLam,
        "innerPartition" => newMu,
        values => theList
        }
    )
skewTableau (Partition,List) := (lam,theList)->(
    skewTableau(lam,new Partition from {},theList)
    )
skewTableau (Partition,Partition) := (lam,mu) -> (
    skewTableau(lam,mu,toList ((sum toList lam - sum toList mu):0))
    )
skewTableau Partition := lam -> (
    skewTableau(lam,new Partition from {},toList ((sum toList lam):0))
    )

shape = method(TypicalValue => Sequence)
shape SkewTableau := T -> (
    (new Partition from delete(0,toList(T#"outerPartition")),new Partition from delete(0,toList(T#"innerPartition")))
    )

shape0 = method(TypicalValue => Sequence)
shape0 SkewTableau := T -> (
    (T#"outerPartition",T#"innerPartition")
    )
shape0 (Partition,Partition) := (lam,mu) -> (
    shape0 skewTableau(lam,mu)
    )

reducedShape = method(TypicalValue => Sequence)
reducedShape SkewTableau := T -> (
    (lam,mu) := shape0 T;

    if mu#-1 == 0 then return shape T;

    lamNew := delete(0,for thePart in lam list thePart - mu#-1);
    muNew := delete(0,for thePart in mu list thePart - mu#-1);

    (new Partition from lamNew, new Partition from muNew)
    )

SkewTableau^ZZ := (T,rowIndex) -> (
    (lam,mu) := shape0 T;

    if rowIndex < 0 then (
        rowIndex = #lam + rowIndex;
        );

    if rowIndex >= #lam then error "index out of bounds";
    
    numBoxesAbove := sum for i from 0 to rowIndex-1 list (lam#i-mu#i);
    ans := toList(mu#rowIndex:null);
    ans = ans|(for i from numBoxesAbove to numBoxesAbove+lam#rowIndex-mu#rowIndex-1 list T#values#i);
    ans
    )

SkewTableau_ZZ := (T,colIndex) -> (
    ans := {};

    (lam,mu) := shape0 T;

    if colIndex < 0 then (
        colIndex = lam#0 + colIndex;
        );

    if colIndex >= lam#0 or colIndex < 0 then error "index out of bounds";

    for i from 0 to #lam-1 do (
        if colIndex < mu#i then (
            ans = ans|{null};
            ) else if (colIndex >= lam#i) then (
            break
            ) else (
            numBoxesAbove := sum for j from 0 to i-1 list (toList lam - toList mu)#j;
            numBoxesLeft := colIndex-mu#i;
            ans = ans|{T#values#(numBoxesAbove+numBoxesLeft)};
            );
        );
    ans
    )

SkewTableau_Sequence := (T,thePosition)->(
    (rowIndex,colIndex) := thePosition;
    ans := T^rowIndex#colIndex;
    if ans === null then error "index out of range";
    ans
    )

pretty SkewTableau := T -> (
    fixedBoxWidth := true;
    muFiller := " "; --or "░"
    
    (lam,mu) := shape0 T;

     if size T == 0 then return "∅";

    colList := for colIndex from 0 to lam#0-1 list (
        currCol := T_colIndex;
        colWidth := max for theBox in currCol list (
            if theBox === null then (
                1
                ) else (
                #toString(theBox)
                )
            );
        if fixedBoxWidth then colWidth = max for theBox in entries T list(
            if theBox === null then (
                1
                ) else (
                #toString(theBox)
                )
            );
        
        currColNet := if (colIndex >= mu#0 and colIndex < lam#0) then concatenate(colWidth:"─") else " ";
        
        for rowIndex from 0 to #currCol-1 do (
            theBox := currCol#rowIndex;
            nextBox := if rowIndex == #currCol-1 then null else currCol#(rowIndex+1);
            boxString := if theBox === null then concatenate(colWidth:muFiller) else toString theBox;
            boxSep := if ((theBox =!= null and rowIndex == #currCol-1) or nextBox =!= null) then concatenate(colWidth:"─") else " ";
            
            currColNet = currColNet||boxString||boxSep;
            );
        currColNet
        );

    sepList := for colIndex from 0 to lam#0 list (
        leftCol := if colIndex == 0 then null else T_(colIndex-1);
        rightCol := if colIndex == lam#0 then null else T_(colIndex);

        currSepNet := if (colIndex > mu#0 and colIndex < lam#0) then (
            "┬"
            ) else if (colIndex == mu#0 and colIndex < lam#0) then (
            "┌"
            ) else if (colIndex > mu#0 and colIndex == lam#0) then (
            "┐"
            ) else (
            " "
            );
        
        for rowIndex from 0 to #lam-1 do (
            isBoxLeft := leftCol =!= null and rowIndex < #leftCol and leftCol#rowIndex =!= null;
            isBoxRight := rightCol =!= null and rowIndex < #rightCol and rightCol#rowIndex =!= null;

            isBoxLeftDown := leftCol =!= null and rowIndex+1 < #leftCol and leftCol#(rowIndex+1) =!= null;
            isBoxRightDown := rightCol =!= null and rowIndex+1 < #rightCol and rightCol#(rowIndex+1) =!= null;
            

            sepString := if isBoxLeft or isBoxRight then "│" else " ";

            nextUp := isBoxLeft or isBoxRight;
            nextDown := isBoxLeftDown or isBoxRightDown;
            nextLeft := isBoxLeft or isBoxLeftDown;
            nextRight := isBoxRight or isBoxRightDown;
            
            nextSep := if nextUp and nextDown and nextLeft and nextRight then (
                "┼"
                ) else if nextUp and nextDown and nextLeft then (
                "┤"
                ) else if nextUp and nextDown and nextRight then (
                "├"
                ) else if nextUp and nextLeft and nextRight then (
                "┴"
                ) else if nextUp and nextLeft then (
                "┘"
                ) else if nextUp and nextRight then (
                "└"
                ) else if nextDown and nextLeft and nextRight then (
                "┬"
                ) else if nextDown and nextLeft then (
                "┐"
                ) else if nextDown and nextRight then (
                "┌"
                ) else (
                " "
                );
            
            
            currSepNet = currSepNet||sepString||nextSep;
            );
        currSepNet
        );
    

    ans := "";
    for theNet in mingle {sepList,colList} do (
        ans = ans|theNet;
        );
    ans
    )

net SkewTableau := T -> (
    (lam,mu) := shape0 T;

    if sum toList lam - sum toList mu == 0 then return "∅";
    
    colList := for colIndex from 0 to lam#0-1 list (
        currCol := T_colIndex;
        currColNet := " ";
        if all(currCol, theBox -> theBox === null) then (
            for i from 0 to #currCol-1 do (
                currColNet = currColNet||" "; --or "░"
                );
            ) else (
            colWidth := max for theBox in currCol list (
                if theBox === null then (
                    0
                    ) else (
                    #toString(theBox)
                    )
                );
            if colIndex >= mu#0 then (
                currColNet = concatenate (colWidth:"_");
                );
            for rowIndex from 0 to #currCol-1 do (
                theBox := currCol#rowIndex;
                if theBox === null then (
                    if colIndex <= mu#rowIndex and rowIndex < #mu-1 and colIndex >= mu#(rowIndex+1) then (
                        currColNet = currColNet||(concatenate (colWidth:"_"));
                        ) else (
                        currColNet = currColNet||" ";
                        );
                    ) else (
                    currColNet = currColNet||toString(theBox);
                    );
                );
            currColNet = currColNet||(concatenate (colWidth:"¯"));
            );
        currColNet
        );
    
    colSepList := for colIndex from 0 to lam#0-1 list (
        rowNetList := for rowIndex from 0 to #lam-1 list (
            if colIndex == mu#rowIndex xor colIndex == lam#rowIndex then (
                "|"
                ) else (
                " "
                )
            );
        currCol := "";
        for theRowNet in rowNetList do (
            currCol = currCol||theRowNet;
            );
        currCol
        );
    lastColSep := " ";
    for i from 0 to #lam-1 do (
        if lam#i == lam#0 and lam#i > mu#i then (
            lastColSep = lastColSep||"|";
            ) else if lam#i == lam#0 and lam#i == mu#i then (
            lastColSep = lastColSep||" ";
            ) else (
            break;
            );
        );
    colSepList = append(colSepList,lastColSep);
    

    ans := colSepList#0;
    if mu#-1 > 0 then (
        ans = "";
        );
    for i from 0 to #colList-1 do (
        ans = ans|colList#i|colSepList#(i+1);
        );
    ans^1
        
    )

entries SkewTableau := T -> T#values

numcols SkewTableau := T -> (T#"outerPartition")#0

numrows SkewTableau := T -> #T#"outerPartition"

size SkewTableau := T -> # entries T

toList SkewTableau := T -> (
    for i from 0 to #T#"outerPartition"-1 list T^i
    )

conjugate SkewTableau := T -> (
    (lam,mu) := shape0 T;
    
    lam' := conjugate lam;
    mu' := conjugate mu;
    entryList' := flatten for colIndex from 0 to lam#0-1 list colEntries(colIndex,T);

    skewTableau(lam',mu',entryList')
    )

components SkewTableau := T -> (
    (lam,mu) := shape0 T;

    componentStarts := select(0..(#lam-1),i -> if lam#i == mu#i then (false) else (i == 0 or lam#i <= mu#(i-1)));
    componentEnds := select(0..(#lam-1),i -> if lam#i == mu#i then (false) else (i == #lam-1 or mu#i >= lam#(i+1)));

    for i from 0 to #componentStarts-1 list (
        partIndices := toList((componentStarts#i)..(componentEnds#i));
        lam' := new Partition from for theIndex in partIndices list (lam#theIndex-mu#(partIndices#-1));
        mu' := new Partition from for theIndex in partIndices list (mu#theIndex-mu#(partIndices#-1));
        entryList' := flatten for theIndex in partIndices list rowEntries(theIndex,T);
        skewTableau(lam',mu',entryList')
        )
    
    --(componentStarts,componentEnds)
    )

SkewTableau == SkewTableau := (T1,T2) -> (
    if entries T1 != entries T2 then return false;
    
    (lam1,mu1) := toSequence reducedShape T1;
    (lam2,mu2) := toSequence reducedShape T2;

    return toList lam1 == toList lam2 and toList mu1 == toList mu2;
    )

rowEntries = method(TypicalValue => List)
rowEntries (ZZ,SkewTableau) := (rowIndex,T) -> delete(null,T^rowIndex)

colEntries = method(TypicalValue => List)
colEntries (ZZ,SkewTableau) := (colIndex,T) -> delete(null,T_colIndex)

isSkew = method(TypicalValue => Boolean)
isSkew SkewTableau := T -> (#((shape T)#1) > 0)

-*
toYoungTableau = method(TypicalValue => YoungTableau)
toYoungTableau SkewTableau := T -> (
    newEntries := for i from 0 to numRows T - 1 list (
        for theBox in T^i list (
            if theBox === null then (
                0
                ) else (
                theBox
                )
            )
        );
    listToTableau newEntries
    )
*-

indexToPosition = method(TypicalValue => Sequence)
indexToPosition (ZZ,SkewTableau) := (theIndex,T) -> (
    if theIndex < 0 then (
        theIndex = size T + theIndex;
        );
    if theIndex < 0 or theIndex >= size T then error "index out of range";

    (lam,mu) := shape0 T;

    numBoxesSeen := 0;
    for rowIndex from 0 to numRows T - 1 do (
        for colIndex from mu#rowIndex to lam#rowIndex - 1 do (
            if numBoxesSeen == theIndex then return (rowIndex,colIndex);
            numBoxesSeen = numBoxesSeen + 1;
            );
        );
    )


positionToIndex = method(TypicalValue => ZZ)
positionToIndex (Sequence,SkewTableau) := (thePosition,T) -> (
    (rowIndex,colIndex) := thePosition;
    --rowIndex := thePosition#0;
    --colIndex := thePosition#1;
    (lam,mu) := shape0 T;

    if rowIndex > #lam-1 or colIndex < mu#rowIndex or colIndex >= lam#rowIndex then error "index out of range";

    numBoxesSeen := 0;
    for theRowIndex from 0 to numRows T - 1 do (
        for theColIndex from mu#theRowIndex to lam#theRowIndex - 1 do (
            if (theRowIndex,theColIndex) == (rowIndex,colIndex) then return numBoxesSeen;
            numBoxesSeen = numBoxesSeen + 1;
            );
        );
    )



-*
columnStabilizer
rowStabilizer
firstRowDescent
readingWord
--semistandardTableaux
standardTableaux
firstRowDescent
*-

maxSSYT = method(TypicalValue => SkewTableau)
maxSSYT (Partition,Partition) := (lam,mu) -> (
    tempT := skewTableau(lam,mu);
    (lam,mu) = shape0 tempT;

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
    (lam,mu) = shape0 tempT;
    
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
    (lam,mu) := shape0 T;
    (rowIndex,colIndex) := thePosition;
    
    if (rowIndex < 0) or (rowIndex >= #lam) then error "index out of range";
    if (colIndex < mu#rowIndex) or (colIndex >= lam#rowIndex) then error "index out of range";

    entryList := new MutableList from entries T;

    for currRowIndex from rowIndex to #T_colIndex-1 do (
        for currColIndex from colIndex to #T^currRowIndex-1 do (
            theIndex := positionToIndex((currRowIndex,currColIndex),T);
            
            currBox := entryList#theIndex;
            leftBox := 0;
            aboveBox := 0;
            if currColIndex > mu#currRowIndex then (
                leftIndex := positionToIndex((currRowIndex,currColIndex-1),T);
                leftBox = entryList#leftIndex;
                );
            if currRowIndex > number(T_currColIndex,theBox -> theBox === null) then (
                aboveIndex := positionToIndex((currRowIndex-1,currColIndex),T);
                aboveBox = entryList#aboveIndex;
                );
            
            if thePosition == (currRowIndex,currColIndex) or currBox < leftBox or currBox <= aboveBox then (
                if currBox >= minSSYT_(currRowIndex,currColIndex) then return null;
                entryList#theIndex += 1;
                );
            );
        );

    skewTableau(lam,mu,toList entryList)
    )

allSSYT = method(TypicalValue => List)
allSSYT (Partition,Partition,ZZ) := (lam,mu,maxEntry) -> (
    T := skewTableau(lam,mu);

    (lam,mu) = shape0 T;
    (lam',mu') := shape0 conjugate T;

    if any(0..(lam#0-1),i -> #colEntries(i,T) > maxEntry) then return {};

    maxT := maxSSYT(lam,mu);
    minT := minSSYT(lam,mu,maxEntry);
    ans := {maxT};

    counter := 0;

    recurse := (theIndex,T) -> (
        newT := addOneSSYT(T,indexToPosition(theIndex,T),minT);
        
        if newT =!= null then (
            ans = append(ans,newT);
            
            for i from 1 to -theIndex do (
                recurse(-i,newT)
                );
            );
        );

    for theIndex from 1 to size T do (
        recurse(-theIndex,maxT);
        );
    
    ans
    )
allSSYT (Partition,Partition) := (lam,mu) -> (
    maxEntry := #(delete(0,toList lam));
    allSSYT(lam,mu,maxEntry)
    )
allSSYT (Partition,ZZ) := (lam,maxEntry) -> (
    mu := new Partition from {0};
    allSSYT(lam,mu,maxEntry)
    )
allSSYT Partition := lam -> (
    mu := new Partition from {0};
    maxEntry := #(delete(0,toList lam));
    allSSYT(lam,mu,maxEntry)
    )
