(* ::Package:: *)

(* ::Chapter:: *)
(*Density matrix reconstruction*)


(* ::Subtitle:: *)
(*Density matrix reconstruction based on Maximum Likelihood Estimation (MLE)*)


(* ::Subchapter:: *)
(*Data acquisition*)


(* ::Input::Initialization:: *)
getIndex::usage="Provided that 'data' is a list of strings, finds a line that matches string pattern 'pattern' and returns its index.";


(* ::Input::Initialization:: *)
getIndex[data_,pattern_]:=Module[{i=1},
Scan[If[StringMatchQ[#,pattern],Return[i],i++]&,data]
]


(* ::Input::Initialization:: *)
getDiagonalElements::usage="Takes a list of strings containing loaded data and returns association containing data pertaining to a diagonal of a density matrix";


(* ::Input::Initialization:: *)
getDiagonalElements[strlist:{__String}]:=
Module[{startsec,startdata,enddata,data,rawdata,specs,assocData},
startsec=getIndex[strlist,___~~"Diagonal elements"~~___];
startdata=getIndex[strlist[[startsec;;]],___~~"Singles 1"~~___];
enddata=1+getIndex[strlist[[startsec+startdata;;]],""];
data=strlist[[startsec+startdata;;startsec+enddata]];
rawdata=StringCases[#,{"<"~~Shortest[x__]~~"|"~~__~~">"~~Whitespace~~s1:NumberString~~Whitespace~~s2:NumberString~~Whitespace~~c:NumberString~~___:>ToExpression/@{"{"<>x<>"}",s1,s2,c}}]&/@data;
specs=rawdata[[All,1,1]];
rawdata=rawdata[[All,1,2;;]];
assocData=Association@Thread[specs->rawdata];
<|"startSecIndex"->startsec,"startDataIndex"->startsec+startdata,"endDataIndex"->startsec+enddata,"dataString"->data,"specs"->specs,"assocData"->assocData,"rawData"->rawdata|>
]


(* ::Input::Initialization:: *)
getOffDiagonalElements::usage="Takes a list of strings containing loaded data and returns association containing data pertaining to offdiagonal terms of a density submatrix.";


(* ::Input::Initialization:: *)
getOffDiagonalElements[strlist:{__String}]:=Module[{startsec,ind,row,col,secpatt,specs,offset,data,rawdata,stringbounds,elemspecs,assocData},
secpatt=___~~"<"~~Shortest[row__]~~"|"~~___~~"|"~~Shortest[col__]~~">"~~___;
startsec=getIndex[strlist,___~~"Off-diagonal elements"~~___];

ind=MapIndexed[{#2,StringMatchQ[#1,secpatt]}&,strlist[[startsec;;]]];
ind=startsec-1+Pick[ind[[All,1,1]],ind[[All,-1]]];

offset=getIndex[strlist[[ind[[1]];;]],___~~"Singles 1"~~___];
rawdata=Table[(data=strlist[[Span@@(elem+offset+7 set+{1,4})]];
StringSplit[#,Whitespace]&/@data),{elem,ind},{set,0,3}];
specs=rawdata[[All,All,All,1]];
rawdata=ToExpression@rawdata[[All,All,All,2;;]];

elemspecs=First@Flatten[StringCases[strlist[[ind]],{secpatt:>{ToExpression["{"<>row<>"}"],ToExpression["{"<>col<>"}"]}}],{2}];
stringbounds={startsec,Last@ind+7 4};
assocData=Association@Thread[elemspecs->rawdata];

<|"startSecIndex"->startsec,"startDataIndices"->ind,"dataStringBounds"->stringbounds,"elemSpecs"->elemspecs,"specs"->specs,(*"rawData"\[Rule]rawdata,*)"assocData"->assocData|>
]


(* ::Input::Initialization:: *)
getNondegenerate[counts_Association]:=Select[counts,FreeQ[_Missing]]
getRowDegenerate[counts_Association]:=Module[{data},
data=Select[counts,MatchQ[#[[3,1]],_Missing]&];
data=#[[{1,2},{1,2}]]&/@data;
data
]
getColDegenerate[counts_Association]:=Module[{data},
data=Select[counts,MatchQ[#[[2,1]],_Missing]&];
data=#[[{1,3},{1,2}]]&/@data;
data
]


(* ::Subchapter:: *)
(*Density matrix reconstruction*)


(* ::Section:: *)
(*Data preprocessing*)


(* ::Input::Initialization:: *)
ClearAll[canonicalBasisEquivalent]
canonicalBasisEquivalent::usage="Takes arbitrary number of associations with keys of the form {{\!\(\*SubscriptBox[\(r\), \(1\)]\),...,\!\(\*SubscriptBox[\(r\), \(n\)]\)},{\!\(\*SubscriptBox[\(c\), \(1\)]\),...,\!\(\*SubscriptBox[\(c\), \(m\)]\)}} (for given n and m) and returns equivalent associations whose keys are changed according to transformation rules transfRules.";

canonicalBasisEquivalent[list:__Association]:=canonicalBasisEquivalent[{list}]
canonicalBasisEquivalent[list:{__Association}]:=Module[{keys,rows,cols,rowsIndi,colsIndi,transfRules,assocList=list,rowIndiRules,colIndiRules,rowTransfRules,colTransfRules,specs},
keys=Flatten[Keys/@assocList,1];
{rows,cols}={keys[[All,1]],keys[[All,2]]};

rowsIndi=Union/@Transpose[rows];
colsIndi=Union/@Transpose[cols];

rowIndiRules=Thread[#->Range[Length[#]]]&/@rowsIndi;
colIndiRules=Thread[#->Range[Length[#]]]&/@colsIndi;

rowTransfRules=Rule[#,Table[#[[i]]/.rowIndiRules[[i]],{i,Length[#]}]]&/@Tuples[rowsIndi];
colTransfRules=Rule[#,Table[#[[i]]/.colIndiRules[[i]],{i,Length[#]}]]&/@Tuples[colsIndi];

specs=Tuples[{Tuples[rowsIndi],Tuples[colsIndi]}];
transfRules=Rule[#,{#[[1]]/.rowTransfRules,#[[2]]/.colTransfRules}]&/@specs;
assocList=Map[KeyMap[(#/.transfRules)&],assocList];

{assocList,transfRules}
]


(* ::Input::Initialization:: *)
renormalizeCounts[offdiag_,subspace_]:=Module[{offPlusSubspace,renorm,renormalizeOneTerm},
renormalizeOneTerm[mat_,norm_]:=N[(norm #)/Total[#]]&/@mat;

offPlusSubspace=Association[(#->{offdiag[#],subspace[#]})&/@Keys[offdiag]];
renorm=renormalizeOneTerm[#1,#2]&@@@offPlusSubspace;
renorm
]


(* ::Input::Initialization:: *)
renormalizeOffDiags[offdiag_,subspaceCounts_]:=Module[{offPlusSubspace,reimetc,offre,offim,nondeg,rowdeg,coldeg,nondegren,rowdegren,coldegren,diagpart,nondegpart,rowdegpart,coldegpart,repart,impart},

nondeg=getNondegenerate[offdiag];
rowdeg=getRowDegenerate[offdiag];
coldeg=getColDegenerate[offdiag];

nondegren=renormalizeCounts[nondeg,subspaceCounts];
rowdegren=renormalizeCounts[rowdeg,subspaceCounts];
coldegren=renormalizeCounts[coldeg,subspaceCounts];

{nondegren,rowdegren,coldegren}
]


(* ::Section:: *)
(*Iterative reconstruction*)


(* ::Input::Initialization:: *)
ketbra[i_,j_,d_]:=ReplacePart[ConstantArray[0,{d,d}],{i,j}->1]


(* ::Input::Initialization:: *)
projPhase[i_,j_,d_,\[CurlyPhi]_]:=1/2 (ketbra[i,i,d]+ketbra[j,j,d])+1/2 (Exp[I \[CurlyPhi]]ketbra[j,i,d]+Exp[-I \[CurlyPhi]]ketbra[i,j,d])


(* ::Input::Initialization:: *)
pp[i_,j_,d_:dim]:=projPhase[i,j,d,0]
pm[i_,j_,d_:dim]:=projPhase[i,j,d,\[Pi]]
pip[i_,j_,d_:dim]:=projPhase[i,j,d,\[Pi]/2]
pim[i_,j_,d_:dim]:=projPhase[i,j,d,-(\[Pi]/2)]


(* ::Input::Initialization:: *)
pdiag[i_,d_:dim]:=ketbra[i,i,d]


(* ::Input::Initialization:: *)
get2dProj[row_,col_,oper1_:ketbra,oper2_:ketbra,d_:dim]:=KroneckerProduct[oper1[First@row,First@col,d],oper2[Last@row,Last@col,d]];


(* ::Input::Initialization:: *)
indOper[oper1_,oper2_]:=Sequence@@Switch[{oper1,oper2},
{pp,pp},{1,1},
{pp,pm},{1,2},
{pm,pp},{1,3},
{pm,pm},{1,4},

{pp,pip},{2,1},
{pp,pim},{2,2},
{pm,pip},{2,3},
{pm,pim},{2,4},

{pip,pp},{3,1},
{pip,pm},{3,2},
{pim,pp},{3,3},
{pim,pm},{3,4},

{pip,pip},{4,1},
{pip,pim},{4,2},
{pim,pip},{4,3},
{pim,pim},{4,4},

{ketbra,ketbra},1,

{ketbra,pp},{1,1},
{ketbra,pm},{1,2},
{ketbra,pip},{2,1},
{ketbra,pim},{2,2},

{pp,ketbra},{1,1},
{pm,ketbra},{1,2},
{pip,ketbra},{2,1},
{pim,ketbra},{2,2},

_,Missing["WrongOperator",{oper1,oper2}]
]


(* ::Input::Initialization:: *)
rMatTerm[assoc_,rho_,oper1_,oper2_,d_:dim]:=Module[{},
N@Total[
Module[{proj=get2dProj[#1,#2,oper1,oper2,d],trace,elem},
trace=Tr[rho . proj];
If[trace==0,
ConstantArray[0,Dimensions[rho]],
elem=assoc[{#1,#2}][[indOper[oper1,oper2]]];
(*Print[assoc[{#1,#2}],Spacer[5],elem];*)
((elem proj)/trace)]
]&@@@Keys[assoc]
]
]


(* ::Input::Initialization:: *)
ClearAll[rMat]
rMat[rho_,diagAssoc_:diag,nondegAssoc_:nondegren,rowdegAssoc_:rowdegren,coldegAssoc_:coldegren,totalCounts_:totalCounts,dim_:dim]:=1/totalCounts Module[{d=dim,diagPart,nondegPart,rowdegPart,coldegPart},

diagPart=rMatTerm[diagAssoc,rho,ketbra,ketbra,d];

nondegPart=rMatTerm[nondegAssoc,rho,pp,pp,d]+rMatTerm[nondegAssoc,rho,pp,pm,d]+rMatTerm[nondegAssoc,rho,pm,pp,d]+rMatTerm[nondegAssoc,rho,pm,pm,d];
nondegPart+=rMatTerm[nondegAssoc,rho,pp,pip,d]+rMatTerm[nondegAssoc,rho,pp,pim,d]+rMatTerm[nondegAssoc,rho,pm,pip,d]+rMatTerm[nondegAssoc,rho,pm,pim,d];
nondegPart+=rMatTerm[nondegAssoc,rho,pip,pp,d]+rMatTerm[nondegAssoc,rho,pip,pm,d]+rMatTerm[nondegAssoc,rho,pim,pp,d]+rMatTerm[nondegAssoc,rho,pim,pm,d];
nondegPart+=rMatTerm[nondegAssoc,rho,pip,pip,d]+rMatTerm[nondegAssoc,rho,pip,pim,d]+rMatTerm[nondegAssoc,rho,pim,pip,d]+rMatTerm[nondegAssoc,rho,pim,pim,d];

rowdegPart=rMatTerm[rowdegAssoc,rho,ketbra,pp,d]+rMatTerm[rowdegAssoc,rho,ketbra,pm,d]+rMatTerm[rowdegAssoc,rho,ketbra,pip,d]+rMatTerm[rowdegAssoc,rho,ketbra,pim,d];

coldegPart=rMatTerm[coldegAssoc,rho,pp,ketbra,d]+rMatTerm[coldegAssoc,rho,pm,ketbra,d]+rMatTerm[coldegAssoc,rho,pip,ketbra,d]+rMatTerm[coldegAssoc,rho,pim,ketbra,d];

diagPart+nondegPart+rowdegPart+coldegPart
]


(* ::Input::Initialization:: *)
newRho[oldRho_,diagAssoc_:diag,nondegAssoc_:nondegren,rowdegAssoc_:rowdegren,coldegAssoc_:coldegren,totalCounts_:totalCounts,dim_:dim]:=Module[{new,matr=rMat[oldRho,diagAssoc,nondegAssoc,rowdegAssoc,coldegAssoc,totalCounts,dim]},
new=matr . oldRho . matr;
new/=Tr[new]
]


(* ::Section:: *)
(*Whole process of reconstruction*)


(* ::Input::Initialization:: *)
fullReconstructMatrixMLE[file_,numOfIterations_:50]:=Module[{strin,str,diags,offdiags,densMat,rules},
strin=StringSplit[ReadString[file],"\n"];
str=StringTrim/@strin;
diags=(*Echo@*)getDiagonalElements[str];
offdiags=getOffDiagonalElements[str];
{densMat,rules}=reconstructMatrixMLE[diags,offdiags,numOfIterations];
{densMat,diags,offdiags}
]


(* ::Input::Initialization:: *)
ClearAll[reconstructMatrixMLE]
reconstructMatrixMLE[diags_Association,offdiags_Association,numOfIterations_:20]:=Module[{assocs,diagCoincRenamed,offdiagCoincRenamed,transfRules,subspaceCounts,densitySubmat,structMatSubspaceCounts,offSpec,structMatRaw,nondegren,rowdegren,coldegren,rho0,diag,offdiagCoinc,diagCoinc,dim,totalCounts,dimSqr},

(*preprocess data*)
{diagCoincRenamed,offdiagCoincRenamed,structMatSubspaceCounts,dimSqr,transfRules}=preprocessDataMLE[diags,offdiags];

(*reconstruct matrix*)
densitySubmat=iterativeReconstructionMLE[diagCoincRenamed,offdiagCoincRenamed,structMatSubspaceCounts,dimSqr,numOfIterations];

{densitySubmat,transfRules}
]


(* ::Input::Initialization:: *)
ClearAll[preprocessDataMLE]
preprocessDataMLE[diags_Association,offdiags_Association]:=Module[{diagCoincRenamed,offdiagCoincRenamed,structMatSubspaceCounts,dimSqr,diagCoinc,offdiagCoinc,assocs,transfRules,structMatRaw,offSpec},

(*get diag and offdiag counts*)
diagCoinc=diags["assocData"][[All,3]];
diagCoinc=AssociationThread[Transpose[{Keys[diagCoinc],Keys[diagCoinc]}]->Values[diagCoinc]];
offdiagCoinc=(offdiags["assocData"]/.{}->Missing["NotMeasured"]{1,1,1})[[All,All,All,3]];

(*rename bases*)
{assocs,transfRules}=canonicalBasisEquivalent[diagCoinc,offdiagCoinc];
{diagCoincRenamed,offdiagCoincRenamed}=assocs;

(*get structMat*)
offSpec=Keys[diagCoincRenamed];
offSpec=DeleteDuplicates@Flatten[offSpec,1];
structMatRaw=(*Echo@*)Outer[List,offSpec,offSpec,1,1];
structMatSubspaceCounts=Map[Union@Tuples@Transpose[#]&,Flatten[structMatRaw,1]];
structMatSubspaceCounts=AssociationThread[Flatten[structMatRaw,1]->structMatSubspaceCounts];

dimSqr=Length[offSpec];

{diagCoincRenamed,offdiagCoincRenamed,structMatSubspaceCounts,dimSqr,transfRules}
]


(* ::Input::Initialization:: *)
ClearAll[iterativeReconstructionMLE]
iterativeReconstructionMLE[diagCoincRenamed_,offdiagCoincRenamed_,structMatSubspaceCounts_,dimSqr_,numOfIterations_:10]:=Module[{subspaceCounts,rho0,nondegren,rowdegren,coldegren,diag,totalCounts,dim,densitySubmat},

(*get subspace counts*)
subspaceCounts=Map[Map[diagCoincRenamed[{#,#}]&],structMatSubspaceCounts,{1}];
subspaceCounts=Map[Total,subspaceCounts,{1}];

(*prepare guess of initial density matrix for iterative reconstruction*)
rho0=IdentityMatrix[dimSqr];
rho0/=Tr[rho0];

(*renormalize off-diagonal counts and prepare diagonal terms*)
{nondegren,rowdegren,coldegren}=renormalizeOffDiags[offdiagCoincRenamed,subspaceCounts];
diag=List/@diagCoincRenamed;

(*total counts and dimension*)
totalCounts=Total@Flatten[Values/@{diag,nondegren,rowdegren,coldegren}];
dim=Sqrt[dimSqr];

(*get density matrix*)
densitySubmat=Nest[newRho[#,diag,nondegren,rowdegren,coldegren,totalCounts,dim]&,rho0,numOfIterations];
densitySubmat
]


(* ::Subchapter:: *)
(*Optimization related routines*)


(* ::Text:: *)
(*structMatRaw2D and structMatRaw3D are structMatRaw matrices taken from MLE reconstruction*)


(* ::Input::Initialization:: *)
structMatRaw2D={{{{2,1},{2,1}},{{2,1},{2,2}},{{2,1},{1,1}},{{2,1},{1,2}}},{{{2,2},{2,1}},{{2,2},{2,2}},{{2,2},{1,1}},{{2,2},{1,2}}},{{{1,1},{2,1}},{{1,1},{2,2}},{{1,1},{1,1}},{{1,1},{1,2}}},{{{1,2},{2,1}},{{1,2},{2,2}},{{1,2},{1,1}},{{1,2},{1,2}}}};
structMatRaw3D={{{{2,2},{2,2}},{{2,2},{2,3}},{{2,2},{2,1}},{{2,2},{3,2}},{{2,2},{3,3}},{{2,2},{3,1}},{{2,2},{1,2}},{{2,2},{1,3}},{{2,2},{1,1}}},{{{2,3},{2,2}},{{2,3},{2,3}},{{2,3},{2,1}},{{2,3},{3,2}},{{2,3},{3,3}},{{2,3},{3,1}},{{2,3},{1,2}},{{2,3},{1,3}},{{2,3},{1,1}}},{{{2,1},{2,2}},{{2,1},{2,3}},{{2,1},{2,1}},{{2,1},{3,2}},{{2,1},{3,3}},{{2,1},{3,1}},{{2,1},{1,2}},{{2,1},{1,3}},{{2,1},{1,1}}},{{{3,2},{2,2}},{{3,2},{2,3}},{{3,2},{2,1}},{{3,2},{3,2}},{{3,2},{3,3}},{{3,2},{3,1}},{{3,2},{1,2}},{{3,2},{1,3}},{{3,2},{1,1}}},{{{3,3},{2,2}},{{3,3},{2,3}},{{3,3},{2,1}},{{3,3},{3,2}},{{3,3},{3,3}},{{3,3},{3,1}},{{3,3},{1,2}},{{3,3},{1,3}},{{3,3},{1,1}}},{{{3,1},{2,2}},{{3,1},{2,3}},{{3,1},{2,1}},{{3,1},{3,2}},{{3,1},{3,3}},{{3,1},{3,1}},{{3,1},{1,2}},{{3,1},{1,3}},{{3,1},{1,1}}},{{{1,2},{2,2}},{{1,2},{2,3}},{{1,2},{2,1}},{{1,2},{3,2}},{{1,2},{3,3}},{{1,2},{3,1}},{{1,2},{1,2}},{{1,2},{1,3}},{{1,2},{1,1}}},{{{1,3},{2,2}},{{1,3},{2,3}},{{1,3},{2,1}},{{1,3},{3,2}},{{1,3},{3,3}},{{1,3},{3,1}},{{1,3},{1,2}},{{1,3},{1,3}},{{1,3},{1,1}}},{{{1,1},{2,2}},{{1,1},{2,3}},{{1,1},{2,1}},{{1,1},{3,2}},{{1,1},{3,3}},{{1,1},{3,1}},{{1,1},{1,2}},{{1,1},{1,3}},{{1,1},{1,1}}}};


(* ::Input::Initialization:: *)
ClearAll[fidelityFunction]
fidelityFunction[varsMagn_,varsPhas_,mat_]:=Abs(*Re*)[refStateOpt[varsMagn,varsPhas]\[Conjugate] . mat . refStateOpt[varsMagn,varsPhas]]


(* ::Input::Initialization:: *)
ClearAll[fidelityFunctionDiag]
fidelityFunctionDiag[varsMagn_,varsPhas_,mat_]:=Abs(*Re*)[refStateOptDiag[varsMagn,varsPhas]\[Conjugate] . mat . refStateOptDiag[varsMagn,varsPhas]]


(* ::Input::Initialization:: *)
fidelity[mat1_,mat2_]:=Chop@Tr[mat1 . mat2]


(* ::Input::Initialization:: *)
purity[mat_]:=Module[{locmat=mat},
locmat/=Tr[locmat];
fidelity[locmat,locmat]
]


(* ::Input::Initialization:: *)
getFidelity[mat_,ref_]:=ref\[Conjugate] . mat . ref


(* ::Input::Initialization:: *)
ClearAll[refStateOpt]
refStateOpt[varsMagn_,varsPhas_]:=Module[{magnitudes,phases},
magnitudes=FromPolarCoordinates[{1}~Join~varsMagn];
phases=Exp[I #]&/@varsPhas;
List@@(magnitudes . ({1}~Join~phases))
]


(* ::Input::Initialization:: *)
fullPureStateOptimization[mat_]:=Module[{structMatRaw,ketBasis,len=Length@mat,varsMagn,varsPhas,\[Theta],\[Phi],vars,initValuesMagn,initValuesPhas,dof,constraints,fidVal,fidArgs,optimalRefStateGen,fidArgsDegrees},
(*variables*)
{varsMagn,varsPhas}={Array[\[Theta],{len-1}],Array[\[Phi],{len-1}]};
vars=Flatten[{varsMagn,varsPhas}];
{initValuesMagn,initValuesPhas}={\[Pi]/4&/@varsMagn,0&/@varsPhas};
dof=Transpose[{varsMagn,initValuesMagn}]~Join~Transpose[{varsPhas,initValuesPhas}];
constraints=(0<=#<=2.Pi)&/@vars;

(*optimization*)
{fidVal,fidArgs}=FindMaximum[{Evaluate@fidelityFunction[varsMagn,varsPhas,mat],constraints},dof];
optimalRefStateGen=refStateOpt[varsMagn,varsPhas]/.fidArgs;
optimalRefStateGen/=Norm[optimalRefStateGen];

(*return results*)
structMatRaw=Switch[Length[mat],
9,structMatRaw3D,
4,structMatRaw2D,
_,Missing[]
];
ketBasis=Ket@@@Diagonal[structMatRaw][[All,1]];

Association["densMat"->mat,"varsMagn"->varsMagn,"varsPhas"->varsPhas,"fidVal"->fidVal,"fidArgs"->fidArgs,"optimalRefStateGen"->optimalRefStateGen,"ketBasis"->ketBasis]
]


(* ::Input::Initialization:: *)
ClearAll[refStateOptDiag]
refStateOptDiag[varsMagn_,varsPhas_]:=Module[{magnitudes,phases,vec,len=Length[varsMagn]+1,fullvec},
magnitudes=FromPolarCoordinates[{1}~Join~varsMagn];
phases=Exp[I #]&/@varsPhas;
vec=List@@(magnitudes . ({1}~Join~phases));
fullvec=ConstantArray[0,{len^2}];

Switch[len,
3,fullvec[[{3,5,7}]]=vec,
2,fullvec[[{2,3}]]=vec,
_,fullvec=$Failed
];
fullvec
]


(* ::Input::Initialization:: *)
fullPureStateOptimizationDiag[mat_]:=Module[{structMatRaw,ketBasis,len=Length@mat,varsMagn,varsPhas,\[Theta],\[Phi],vars,initValuesMagn,initValuesPhas,dof,constraints,fidVal,fidArgs,optimalRefStateGen,fidArgsDegrees},
len=Sqrt[len];

(*variables*)
{varsMagn,varsPhas}={Array[\[Theta],{len-1}],Array[\[Phi],{len-1}]};
vars=Flatten[{varsMagn,varsPhas}];
{initValuesMagn,initValuesPhas}={\[Pi]/4&/@varsMagn,0&/@varsPhas};
dof=Transpose[{varsMagn,initValuesMagn}]~Join~Transpose[{varsPhas,initValuesPhas}];
constraints=(0<=#<=2.Pi)&/@vars;

(*optimization*)
{fidVal,fidArgs}=FindMaximum[{Evaluate@fidelityFunctionDiag[varsMagn,varsPhas,mat],constraints},dof];
optimalRefStateGen=refStateOptDiag[varsMagn,varsPhas]/.fidArgs;
optimalRefStateGen/=Norm[optimalRefStateGen];

(*return results*)
structMatRaw=Switch[Length[mat],
9,structMatRaw3D,
4,structMatRaw2D,
_,Missing[]
];
ketBasis=Ket@@@Diagonal[structMatRaw][[All,1]];

Association["densMat"->mat,"varsMagn"->varsMagn,"varsPhas"->varsPhas,"fidVal"->fidVal,"fidArgs"->fidArgs,"optimalRefStateGen"->optimalRefStateGen,"ketBasis"->ketBasis]
]


(* ::Input::Initialization:: *)
getMaximizedOverlapState[optres_]:=Module[{vec=optres["optimalRefStateGen"],len,optperm},
len=Length[vec];
optperm=Switch[len,
9,{1,2,3,4,5,6,7,8,9},
4,{1,2,3,4}(*{1,2,3,4}*),
_,Missing[]
];
vec=vec[[optperm]];
(*{vec}\[ConjugateTranspose].{vec}*)
Transpose[{vec}\[ConjugateTranspose] . {vec}]
]


(* ::Subchapter:: *)
(*Monte Carlo for error estimation*)


(* ::Input::Initialization:: *)
generateSampleDiags[diagCoincRaw_Association,num_Integer?Positive]:=Module[{keys,vals,sample},
{keys,vals}={Keys[diagCoincRaw],Values[diagCoincRaw]};
sample=If[#>0,RandomVariate[PoissonDistribution[#],num],ConstantArray[0.00001,{num}]]&/@vals;
AssociationThread[keys->#]&/@Transpose[sample]
]


(* ::Input::Initialization:: *)
generateSampleOffDiags[offdiagCoinc_Association,num_Integer?Positive]:=Module[{keys,vals,sample,genVals},
{keys,vals}={Keys[offdiagCoinc],Values[offdiagCoinc]};

genVals[mat_]:=
TensorTranspose[
Map[
Which[
#===Missing["NotMeasured"],ConstantArray[Missing["NotMeasured"],{num}],
#==0,ConstantArray[0.00001,{num}],
#>0,RandomVariate[PoissonDistribution[#],num]]&
,mat,{2}]
,{2,3,1}];

sample=genVals/@vals;
sample=TensorTranspose[sample,{2,1,3,4}];
AssociationThread[keys->#]&/@sample
]


(* ::Input::Initialization:: *)
generateSampleMatrix[diagCoinc_,offdiagCoinc_,structMatSubspaceCounts_,num_,dimSqr_,numOfIterations_:50]:=
Module[{diags,offdiags},
diags=generateSampleDiags[diagCoinc,num];
offdiags=generateSampleOffDiags[offdiagCoinc,num];
iterativeReconstructionMLE[#1,#2,structMatSubspaceCounts,dimSqr,numOfIterations]&@@@Transpose[{diags,offdiags}]
]


(* ::Input::Initialization:: *)
monteCarloFidelitiesMLE[{diags_,offdiags_},numOfGenSamples_,numOfIterationsMLE_]:=Module[{diagCoincRenamed,offdiagCoincRenamed,structMatSubspaceCounts,dimSqr,transfRules,matlistRaw,matlist,exc,optres,fids,sqrtpur},
{diagCoincRenamed,offdiagCoincRenamed,structMatSubspaceCounts,dimSqr,transfRules}=preprocessDataMLE[diags,offdiags];

(*time-intensive step:*)
matlistRaw=generateSampleMatrix[diagCoincRenamed,offdiagCoincRenamed,structMatSubspaceCounts,numOfGenSamples,dimSqr,numOfIterationsMLE];

(*exc=Switch[dimSqr,
9,{3,5,7}(*{1,6,8}*),
4,{2,3},
_,All
];
matlist=matlistRaw[[All,exc,exc]];*)
optres=fullPureStateOptimization/@matlistRaw;
fids=optres[[All,"fidVal"]];
sqrtpur=Sqrt@*purity/@matlistRaw(*optres[[All,"densMat"]]*);

{matlistRaw,fids,sqrtpur}
]


(* ::Subchapter:: *)
(*Data reports*)


(* ::Input::Initialization:: *)
ClearAll[reportState]
reportState[mat_,imsize_:Automatic]:=Module[{data},
data={"positive semidef. mat"->PositiveSemidefiniteMatrixQ[mat],"purity"->purity[mat],"\!\(\*SqrtBox[\(purity\)]\)"->Sqrt[purity[mat]],"plot Re"->MatrixPlot[Re@mat,ImageSize->imsize],"plot abs"->MatrixPlot[Abs@mat,ImageSize->imsize]};
Dataset[Association@@data]
]


(* ::Input::Initialization:: *)
plot3Dstate[mat_,reim:(Re|Im):Re]:=densChart`densityMatrixPlot3D[reim@mat,ConstantArray[0,Dimensions[mat]](*,None,Automatic,3*)]


(* ::Input::Initialization:: *)
reportOptimization[assoc_]:=Module[{radsToDegs,data,refst=assoc["optimalRefStateGen"]},
radsToDegs=UnitConvert[Quantity[#,"Radians"],"AngularDegrees"]&;
data={
"magnitudes (angles)"->Map[radsToDegs,{0}~Join~assoc["varsMagn"]/.assoc["fidArgs"]],
"phases"->Chop[Map[radsToDegs,{0}~Join~assoc["varsPhas"]/.assoc["fidArgs"]],1.*^-5],
"state"->refst,
"abs. val. state"->Abs[refst],
"ket"->Chop[assoc["ketBasis"] . refst,1.*^-5],
"fidelity"->assoc["fidVal"],
"\!\(\*SqrtBox[\(purity\)]\)"->Sqrt[purity[assoc["densMat"]]]
};
Dataset[Association@data]
]


(* ::Input::Initialization:: *)
reportMaximizedOverlap[files_,optimres_]:=Module[{data,optimFids,dims,sqrtpur},
optimFids=optimres[[All,"fidVal"]];
dims=Sqrt@*Length/@optimres[[All,"densMat"]];
sqrtpur=Sqrt@*purity/@optimres[[All,"densMat"]];
data=Transpose[{optimFids,sqrtpur,dims}];
TableForm[data,TableHeadings->{files,{"fidelity with optim. state","\!\(\*SqrtBox[\(purity\)]\)","dimension"}}]
]


(* ::Input::Initialization:: *)
reportErrorEstimates[fids_]:=TableForm[Transpose[{Mean/@fids,StandardDeviation/@fids}],TableHeadings->{files,{"mean","std"}}]


(* ::Input::Initialization:: *)
ClearAll[compareStates]
compareStates[mat1_,mat2_,imgsize_:Automatic,lb1_:"mat 1",lb2_:"mat 2"]:=Module[{data,data1,data2,fun},
fun={purity[#],Sqrt[purity[#]],(*MatrixPlot[Re@#,ImageSize\[Rule]imgsize],MatrixPlot[Abs@#,ImageSize\[Rule]imgsize],*)
(*Show[densChart`densityMatrixPlot3D[Re@#,ConstantArray[0,Dimensions[#]]],ImageSize\[Rule]imgsize]*)
BarChart3D[Re@#,ChartLayout->"Grid",ImageSize->imgsize],BarChart3D[Abs@#,ChartLayout->"Grid",ImageSize->imgsize]
}&;
data1=fun[mat1];
data2=fun[mat2];
data=Transpose[{data1,data2}];
TableForm[data,TableHeadings->{{"purity","\!\(\*SqrtBox[\(purity\)]\)","plot Re","plot Abs","plot 3D Re"},{lb1,lb2}}]
]


(* ::Input::Initialization:: *)
ClearAll[compareStatesDiff]
compareStatesDiff[mat1_,mat2_,imgsize_:Automatic,lb1_:"mat 1",lb2_:"mat 2"]:=Module[{data,data1,data2,data3,fun,funD},
fun={purity[#],Sqrt[purity[#]],(*MatrixPlot[Re@#,ImageSize\[Rule]imgsize],MatrixPlot[Abs@#,ImageSize\[Rule]imgsize],*)
(*Show[densChart`densityMatrixPlot3D[Re@#,ConstantArray[0,Dimensions[#]]],ImageSize\[Rule]imgsize]*)
BarChart3D[Re@#,ChartLayout->"Grid",ImageSize->imgsize],
BarChart3D[Im@#,ChartLayout->"Grid",ImageSize->imgsize],
BarChart3D[Abs@#,ChartLayout->"Grid",ImageSize->imgsize]
}&;
funD={"","",(*MatrixPlot[Re@#,ImageSize\[Rule]imgsize],MatrixPlot[Abs@#,ImageSize\[Rule]imgsize],*)
(*Show[densChart`densityMatrixPlot3D[Re@#,ConstantArray[0,Dimensions[#]]],ImageSize\[Rule]imgsize]*)
BarChart3D[Re@#,ChartLayout->"Grid",ImageSize->imgsize],
BarChart3D[Im@#,ChartLayout->"Grid",ImageSize->imgsize],
BarChart3D[Abs@#,ChartLayout->"Grid",ImageSize->imgsize]
}&;
data1=fun[mat1];
data2=fun[mat2];
data3=funD[mat1-mat2];
data=Transpose[{data1,data2,data3}];
TableForm[data,TableHeadings->{{"purity","\!\(\*SqrtBox[\(purity\)]\)","plot Re","plot Im","plot Abs","plot 3D Re"},{lb1,lb2,"Difference"}}]
]


(* ::Input::Initialization:: *)
assessMaxOverlap[idx_,imgsize_:400(*700*)]:=compareStatesDiff(*compareStates*)[matrices[[idx]],maxOverlapStates[[idx]],imgsize,"Reconstructed matrix","Maximized overlap pure state"]


(* ::Input::Initialization:: *)
assessMaxOverlapDiag[idx_,imgsize_:400(*700*)]:=compareStatesDiff[maxOverlapStates[[idx]],maxOverlapStatesDiag[[idx]],imgsize,"Maximized overlap pure state","Maximized overlap pure state Diag"]
