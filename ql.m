(* ::Package::*)
(* :Title:Universal Quantifier Elimination*)
(* :Copyright 2009, 2011 Dr.Timm Lampert*)
(* :Implemented by Michael Taktikos*)
(*Thanks to:Dr.Karsten Mueller for giving important ideas in general programming,
and to Mrs.Lampert and Mrs.Taktikos for their patience that was needed for this work*)

BeginPackage["Timm`"]

tradi::usage = "tradi[x] prints an expression x with quantors ein and alle in TraditionalForm"
untradi::usage = "untradi[x] converts a traditional expression in input form"


(* Begin["`Private`"] *)



(*Nicht vergessen: Erweitung von sat-Diskunktion durch Bezug auf \
k-pairs: Wenn k-pairs={}, dann sat.
Des Weiteren: nenne "standardization" "optimize". Eine \
Standardizierung soll dann die Form der Ausdrücke betreffen: lve, \
variableconverting und expansion muss immer als input der Iterationen \
und optimize vorausgesetzt werden können. Hier kann noch vereinfacht \
und optimiert werden.*)

(*Ordnung der Befehle: Die Befehle auf der obersten Hierarchieebene \
stehen zum Schluß. Wenn man den Ablauf des Programmes verstehen will, \
empfiehlt es sich, das Programm von hinten nach vorne durchzugehen.*)

(* SETATTRIBUTES *)
SetAttributes[And, Orderless];
SetAttributes[Or, Orderless];
(* Von der Ordnung der Elemente der And- und Or-Listen wird \
abgesehen. *)

(*FALSE, TRUE, SAT*)
(*A. ERWEITERUNG VON "False" UND "True"*)
(* Die folgenden Befehle ergänzen die rein aussagenlogisch \
definierten "False" und "True" aus Mathematica. *)
ein[{lv_}, False] := False;
alle[{lv_}, False] := False;
ein[{lv_}, True] := True;
alle[{lv_}, True] := True;

(*B. sat*)
(*"sat" steht für "satisfiable" bzw. genauer: \
"nicht-kontradiktorisch". Der Algorithmus entscheidet, ob ein \
Ausdruck der reinen Quantorenlogisk kontradiktorisch ist oder nicht.
Er leitet erschöpfend explizite Kontradiktionen bzw. explizit \
erfüllbare Ausdrücke ab. Explizite Kontradiktionen werden bereits \
durch Mathematica als "False" kennzeichnet und durch Simplify \
identifiziert.
 "Explizit erfüllbare Ausdrücke" sind solche die keine Allquantoren \
enthalten und nicht False sind. Wir kennzeichnen sie durch "sat" und \
identifizieren sie mittels des Moduls "satExpression".
  Zwecks Optimierung verwenden wir noch das Modul "satDisjunktion", \
das eine Disjunktion als erfüllbar identifiziert, sobald ein Disjunkt \
"sat" ist.*)

satExpression[expression_] := 
  If[FreeQ[Simplify[expression], 
     nonsat] && ((Not[Simplify[expression] === False] && 
        FreeQ[Simplify[expression], alle[{lv__}, etwas_]]) || (Not[
         Simplify[expression] === False] && 
        kpairs[expression] === {} )), sat, expression]; 
(*satExpression identifiziert einen Ausdruck als "sat" (= \
satisfiable, i.e. non-contradictory), wenn er nicht False ist und \
keine Allquantoren mehr enthalten sind oder wenn er nicht False ist \
und keine K-paare enthalten sind. Das Modul setzt nun mit kpairs \
maxIndizierung voraus. (Achtung: Kontrollieren, ob diese Bedingung \
immer erfüllt ist, wenn satExpression aufgerufen wird.*)

ein[{lv_}, sat] := sat; 
alle[{lv_}, sat] := sat;
(* Diese Befehle sind analog zu denen Erweiterungen von "False" und \
"True".*)

satDisjunktion[ausdruck_] :=
  Module[{erg, lae, dd, ohnegeschweifte},
   erg = BooleanMinimize[ausdruck, "DNF"];
   ZPrint["Optimized DNF (1st step of evaluating sat): ", tradi[erg]][
    4]; 
   If[Head[erg] =!= Or, erg = satExpression[erg], lae = Length[erg];
    Do[dd[ii] = satExpression[erg[[ii]]];
     dd[ii] = dd[ii] //. {False} -> False;
     dd[ii] = dd[ii] //. {sat} -> sat;
     If[dd[ii] === sat, erg = sat; Break[]], {ii, 1, lae}];
    If[erg =!= sat, erg = Apply[Or, Table[dd[ii], {ii, 1, lae}]]]];
   ZPrint["result of satDisjunktion: ", tradi[erg]][4];
   erg];
(*"satDisjunktion" identifiziert eine Disjunktion (mit 1 oder mehr \
Disjunkten) als "sat" wenn ein Disjunkt gemäß satExpression als "sat" \
evaluiert wurde.*)

(* UMFORMUNGEN IN PRINTAUSDRÜCKE (tradi) UND EVALUATIONSAUSDRÜCKE \
(untradi) *)
tradi[ausdruck_ ] :=
  Module[{erg},
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[ein[{xx_}, rest_], ein[xx, rest]]] &, ausdruck];
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[alle[{xx_}, rest_], alle[xx, rest]]] &, erg];
   erg = TraditionalForm[erg /. {alle -> ForAll, ein -> Exists}];
   erg];
(* "tradi" formt Mathematica Ausdrücke in logische Ausdrücke zwecks \
Printausgabe an den user um. Doppelte geschweifte Klammern werden \
allerdings als runde ausgegeben.
Deshalb wird in den Printausgaben, in denen geschweifte Klammern \
wichtig sind, Mathematica-Ausdrücke ausgegeben. Mit diesen wird auch \
intern operiert.*)
 untradi[ausdruck__] :=
  Module[{erg},
   erg = 
    InputForm[ausdruck] /. {aa_*bb_ -> aa[bb], ForAll -> alle, 
      Exists -> ein, "\[Exists]" -> ein, "\[ForAll]" -> alle};
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[ein[xx_, rest_] /; Not[ListQ[xx]], 
        ein[{xx}, rest]]] &, erg];
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[alle[xx_, rest_] /; Not[ListQ[xx]], 
        alle[{xx}, rest]]] &, erg];
   erg];
(* "untradi" formt logische Ausdrücke wieder in Mathematica Ausdrücke \
um *)
wf[ausdruck_] :=
  Module[{erg},
   erg = Replace[ausdruck, 
     RuleDelayed[
      alle[{mm__}, aa_], (ForAll[{mm}, aa] /. {ForAll -> alle})], {0, 
      Infinity}];
   erg = Replace[erg, 
     RuleDelayed[
      ein[{mm__}, aa_], (Exists[{mm}, aa] /. {Exists -> ein})], {0, 
      Infinity}];
   erg];
(* "wf" ersetzt ForAll durch "alle" und "Exists" durch "ein" und \
wieder zurück. ForAll / Exists wird Mathematicaintern nur gesetzt, \
wenn diese einen Wirkungsbereich haben.
Durch die doppelte Ersetzung werden Quantoren ohne Wirkungsbereiche \
gelöscht. 
Der Befehl bewirkt also, dass überflüssige Quantoren ohne \
Wirkungsbereich eliminiert werden. wf ist nötig, wenn Umformungen \
u.a. "sat" im Wirkungsbereich von Quantoren erzeugen. Beispiel: \
decide[alle[{x},ein[{y},o[x,y]\[And]p[y]]]].*)

(*NICHT LOGISCH-SPEZIFISCHE HILFSBEFEHLE*)
SubsetQ[ll1_List, ll2_List] := 
  Sort[Intersection[ll1, ll2]] == Sort[ll1];
SubsetQ[{}, x_] := True;
(* "SubsetQ" fragt, ob "ll1_List" Teilmenge von "ll2_List" ist.
SubsetQ stammt aus Combinatorica-Package von Mma im Verzeichnis \
AddOns\LegacyPackages\DiscreteMath.
Die zweite Zeile, die angibt, daß die leere Menge Teilmenge jeder \
Menge ist, hat keinerlei Auswirkung auf das Logikprogramm und wurde \
nur aufgenommen, damit Kritiker keinen inkompletten SubsetQ-Befehl \
monieren.*)
listenform[ausdruck_] := 
  Table[ausdruck[[ii]], {ii, 1, Length[ausdruck]}];
(* "listenform" listet alle Elemente von "ausdruck" auf (in \
Mathematica ist jeder Ausdruck selbst eine Liste mit einem Kopf). *)
unabhaengigQ[ausdruck_, pliste_] := 
  Apply[And, 
   Table[FreeQ[ausdruck, pliste[[ii]]], {ii, 1, Length[pliste]}]];
(* "unabhaengigQ" fragt, ob "ausdruck" frei von all den Elemente von \
"pListe" ist. *)


(* LOGISCHE HILFSBEFEHLE *)
(* A. ALLGEMEINE LOGISCHE HILFSBEFEHLE *)

LiteralQ[expression_] := 
  FreeQ[expression, And] && FreeQ[expression, Or] && 
   FreeQ[expression, ein] && FreeQ[expression, alle] && 
   Not[NumberQ[expression]] && (Head[expression] =!= 
     List) && (ersterBuchstabe[expression] =!= 
     x) && (ersterBuchstabe[expression] =!= 
     y) && (Head[ersterBuchstabe[expression]] === Symbol);
(*LiteralQ identifiziert Literale. 
LiteralQ identifiziert für jedes negierte Literal auch noch ein \
nicht-negiertes Literal. Um dies auszuschliessen, müssen wir in \
posList negierte Literale durch "ooo" ersetzen und die entsprechenden \
Teilausdrücke nicht als positive Literale identifizieren.*)

posList[expression_] :=
  Module[{expr, poslit},
   expr = expression;
   expr = expr //. Not[x_] -> ooo;
   ZPrint["expression with negative literals replaced by ooo: ", 
     expr][5];
   poslit = 
    DeleteDuplicates[
     Cases[expr, 
      partialexpr_ /; (LiteralQ[partialexpr] && 
         partialexpr =!= ooo), {0, Infinity}]];
   ZPrint["list of unnegated literals: ", poslit][5]; poslit];
(*posList identifiziert die nicht-negierten Literale in einem \
Ausdruck. Um nicht positive Literale zu identifizieren, die negiert \
sind, werden vorher alle negierten Literale durch einen Trick in \
"ooo"-Literale umgeformt, die nicht identifiziert werden.*)
negList[expression_] := 
  DeleteDuplicates[
   Cases[expression, 
    Not[partialexpr_ /; LiteralQ[partialexpr]], {0, Infinity}]];
(*negList identifiziert die negierten Literale in einem Ausdruck.*)

kconditionQ[poslit_ /; (LiteralQ[poslit] && Head[poslit] =!= Not), 
   Not[neglit_] /; LiteralQ[Not[neglit]]] := 
  Module[{value, akt1, akt2},
   value = True;
   If[(Head[poslit] =!= Head[neglit]) ||  (Length[poslit] =!= 
       Length[neglit]), Return[False]];
   Do[akt1 = neglit[[ii]]; akt2 = poslit[[ii]];
    If[((ersterBuchstabe[akt1] === 
          y) && ((ersterBuchstabe[akt2] =!= x ) && (akt1 =!= 
            akt2))) ||
      ((ersterBuchstabe[akt2] === 
          y) && ((ersterBuchstabe[akt1] =!= x ) && (akt1 =!= akt2))), 
     value = False; Break[]]
    , {ii, 1, Length[poslit]}];
   value];
(*kconditionQ prüft, ob zwei Literale die Bedingungen für K-Paare \
erfüllen: Sie müssen dieselben Köpfe und dieselbe Anzahl an \
Argumenten haben und an jeder n-ten Argumentstelle entweder \
identische Argumente haben oder an mindestens einer der beiden \
Argumentstelle eine x-Variable. Wir setzen in diesem Modul \
maxIndizierung voraus.*)
kparts[posList_ , negList_] :=
  Module[{akt1, akt2, erg},
   erg = {};
   Do[akt1 = posList[[ii]];
    Do[akt2 = negList[[jj]]; 
     If[kconditionQ[akt1, akt2], 
      erg = Append[erg, {akt1, akt2}]] , {jj, 1, 
      Length[negList]}], {ii, 1, Length[posList]}]; 
   ZPrint["kpairs: ", erg][4];
   erg];
(*kparts bildet aus einer Liste nicht-negierter Literale und einer \
Liste negierter Literale eine Liste von K-pairs.*)
kpairs[expression_] :=
  Module[{neglist, poslist, kpairlist},
   neglist = negList[expression];
   ZPrint["list of negated literals: ", neglist][5];
   poslist = posList[expression];
   kpairlist = kparts[poslist, neglist];
   kpairlist];
(*kpairs bildet aus einem Ausdruck alle möglichen K-pairs. Dieses \
Modul setzt maxIndizierung voraus!*)

(*B. LOGISCHE OPTIMIERUNGEN*)

(*B1 maxIndizierung*)
(*Der Befehl maxIndizierung, der Ziel der folgenden Definitionen ist, \
ersetzt Variablen, so dass allquantifizierte Variablen x-Variable und \
existenzquantifizierte y-Variable sind und diese Variablen so \
indiziert sind, dass 
jeder Quantor durch seine Variable eindeutig identifiziert werden \
kann. Er wird zwecks Übersichtlichkeit einmal am Anfang des \
Algorithmus nach der Eingabeprüfung verwendet. Vor allem wird er \
immer zu Beginn von qe und em angewendet, um innerhalb dieser Module \
Quantoren durch ihre Variable identifizieren zu können.*)

indicesToSameLevel[kk_[jj__]] := 
  kk[jj] //. gg_[vv_][ww__] -> gg[vv, ww]; 
(*"indicesToSameLevel" schreibt mehrere Indices in eine eckige \
Klammer: z.B. [1,2,3] statt [1][2][3].*)
indicesToOriginalLevel[
   kk_[ll__ /; (Union[ Map[Head, {ll}]] === {Integer})]] := 
  Module[{erg = kk}, Do[erg = erg[{ll}[[ii]]], {ii, 1, Length[{ll}]}];
   erg];
 (* indicesToOriginalLevel[kk_[]]:=kk[];
indicesToOriginalLevel[kk_]:=kk; *)

maxIndizierung[expression_] :=
  Module[{erg, xs, ys},
   erg = expression; xs = 0; ys = 0;
   erg = erg //. {x -> xx, y -> yy};
   erg = erg //. (alle[{lv_ }, 
         innen_] /; (Head[lv] =!= x) || (Length[lv] != 1) || 
         If[Length[lv] == 1, 
          Not[IntegerQ[First[lv]] && (First[lv] > 0)]]) :> (alle[{lv},
          innen] /. lv -> x[++xs]);
   erg = erg //. (ein[{lv_ }, 
         innen_] /; (Head[lv] =!= y) || (Length[lv] != 1) || 
         If[Length[lv] == 1, 
          Not[IntegerQ[First[lv]] && (First[lv] > 0)]]) :> (ein[{lv}, 
         innen] /. lv -> y[++ys]);
   erg];

qseq[expression_] :=
  Module[{inmost, akt, seq, aktseq},
   inmost = 
    Cases[expression, 
     quantor_[{var_}, 
       scope_] /; ((quantor === alle || quantor === ein) && 
        FreeQ[scope, ein] && FreeQ[scope, alle]), {0, Infinity}];
   seq = {};
   Do[aktseq = 
     Cases[expression, 
      partialexpr_ /; ((Head[partialexpr] === alle || 
           Head[partialexpr] === ein) && 
                 Not[FreeQ[partialexpr, inmost[[jj]]]]), {0, 
       Infinity}];(* Print["aktseq = ", aktseq];*) 
    aktseq = 
     Flatten[Reverse[
       Table[First[aktseq[[ii]]], {ii, 1, Length[aktseq]}]]];(* Print[
    "aktseq = ", aktseq];*) 
    seq = Append[seq, aktseq](* ; Print["new sequences: ",
    seq]*), {jj, 1, Length[inmost]}];
   (* Print["sequences: ", seq]; *)
   seq];

minIndizierung[expression_] := 
  Module[{expr, negexpr, qs, lae, akt, newqs, xx, yy}, 
   expr = lve[expression];
   expr = maxIndizierung[expr];
   ZPrint[
     "expression with maximal indices to be converted to minimal \
indices: ", tradi[expr]][4];
   negexpr = 
    ReplaceRepeated[expr, RuleDelayed[x[uu_ /; uu > 0], x[-uu]]];
   negexpr = 
    ReplaceRepeated[negexpr, RuleDelayed[y[vv_ /; vv > 0], y[-vv]]];
   expr = negexpr;
   qs = qseq[negexpr];
   ZPrint["quantor sequences identified by their variables: ", qs][4];
   newqs = qs;
   Do[xx = 0; yy = 0;
    Do[akt = newqs[[ii]][[jj]];
     If[Head[akt] === x, newqs[[ii]][[jj]][[1]] = ++xx, 
      newqs[[ii]][[jj]][[1]] = ++yy];
     expr = 
      ReplaceRepeated[expr, Rule[qs[[ii]][[jj]], newqs[[ii]][[jj]]]]
     (* expr=MapAll[ReplaceRepeated[#,Rule[qs[[ii]][[jj]],
     newqs[[ii]][[jj]]]]&,expr] *), {jj, 1, Length[qs[[ii]]]}], {ii, 
     1, Length[qs]}];
   ZPrint["new list of variables: ", newqs][4];
   ZPrint[
     "quantifiers re-indexed to the minimum number of indices : ", 
     tradi[expr]][4];
   expr];

(*DIE FUNKTION le*)
(* "le" steht für "logical equivalence". le ist eine wesentliche \
Funktion des Algorithmus. Durch le werden Formeln in optimierte \
Disjunktionen von Konjunktionen geschlossener Strukturen (= \
distribute normal forms of FOL, kurz DNFFOL) durch reine \
Äquivalenzumformungen gebracht.
Das Programm formt gleich zu Beginn im Rahmen des Moduls \
"standardization" den input-Ausdruck durch le um. Anschließend werden \
im Wesentlichen nur noch die Funktionen qe und em iteriert. le bzw. \
standardization ist Bestandteil von qe und le: le garantiert, dass \
der output von qe und le Listen von DNFFOL sind.
le sorgt dafür, dass die Wirkungsbereiche der Quantoren minimiert \
werden. Demzufolge werden die PN-Gesetze in umgekehrter Reihenfolge \
wie bei der Bildung pränexer Normalformen angewendet. Deshalb baut le \
wesentlich auf pn auf.*)

(*A. pn*)
(* A .1. HILFSBEFEHLE FÜR PN-BEFEHLE*)
alleimp[alle[{ll__}, innen_]] := Module[{innenAkt, lvAkku},
   innenAkt = innen; lvAkku = {ll};
   While[Head[innenAkt] === alle, 
    lvAkku = Flatten[Join[lvAkku, First[innenAkt]]]; 
    innenAkt = First[Rest[innenAkt]] ];
   alle[Sort[lvAkku], innenAkt]];
einimp[ein[{ll__}, innen_]] := Module[{innenAkt, lvAkku},
   innenAkt = innen; lvAkku = {ll};
   While[Head[innenAkt] === ein, 
    lvAkku = Flatten[Join[lvAkku, First[innenAkt]]]; 
    innenAkt = First[Rest[innenAkt]] ];
   ein[Sort[lvAkku], innenAkt]];
(*Die vorangegangen Befehle "implodieren" Quantorenketten, d.h. \
anstelle von alle[{x[1]},alle[{x[2]}, ...]] wird \
alle[{x[1],x[2]},...] geschrieben. Analog für die anderen Fälle.*)
alleexp[alle[{ll__}, innen_]] := 
  Fold[alle[{#2}, #1] &, innen, Reverse[{ll}]];
einexp[ein[{ll__}, innen_]] := 
  Fold[ein[{#2}, #1] &, innen, Reverse[{ll}]];
(*Die vorangegangen Befehle "explodieren" Quantorenketten, d.h. \
anstelle von alle[{x[1],x[2]},...] wird alle[{x[1]},alle[{x[2]}, \
...]] geschrieben. Analog für die anderen Fälle.*)
allepos[alle[lv_List, innen_]] :=
  Module[{llv, lvb, clv, lvbs, erg},
   llv = Length[lv];
   Do[lvb = Select[innen, Not[FreeQ[#, lv[[ii]]]] &];
    clv[ii] = 1;
    If[lvb == True, clv[ii] = 0];
    If[((Head[lvb] === And) || (Head[lvb] === Or)), 
     clv[ii] = Length[lvb]], {ii, 1, llv}];
   lvb = Table[{lv[[ii]], clv[ii]}, {ii, 1, llv}];
   lvbs = Sort[lvb, #1[[2]] >= #2[[2]] &];
   erg = Table[lvbs[[ii, 1]], {ii, 1, llv}];
   alle[erg, innen]];
(* allepos nimmt einen input, der mit einem Allquantor beginnt, und \
sortiert die Laufvariablen dieses Allquantors nach der Häufigkeit \
ihres Auftretens in den verschiedenen Teilausdrücken, d.h. wenn der \
input aus zwei Teilausdrücken besteht, tritt eine Laufvariable \
häufiger auf, die je einmal in jedem der beiden Teilausdrücke \
auftaucht, als eine Laufvariable, die zehnmal in nur einem der \
Teilausdrücke vorkommt. Um dies zu bewerkstelligen, erzeugen wir eine \
Do-Schleife, die über die Anzahl llv der eingegebenen Laufvariablen \
lv läuft und jeweils die Anzahl clv[i] der von der i-ten \
Laufvariablen nicht unabhängigen Teilausdrücke feststellt. Nach der \
Schleife erzeugen wir dann die Auflistung lvb aus der Anzahl llv \
Paaren, die je aus der i-ten Laufvariable und der entsprechenden \
Anzahl clv[i] bestehen, sortieren dann diese Paare so, dass \
diejenigen mit größeren Anzahlen clv[i] den Vorrang bekommen, listen \
daraus das Ergebnis erg der sortierten Laufvariablen auf, und der \
output ist dann gleich dem input, nur mit sortierten Laufvariablen. \
Beispiel: 
allepos[alle[{x1,x2,x4},(f[x1] && g[x2]) ||(j[x2] && h[x3]) && k[x2] || \
l[x2] ]]
alle[{x2,x1,x4},(f[x1]&&g[x2])||(j[x2]&&h[x3]&&k[x2])||l[x2]] *)  
einpos[ein[lv_List, innen_]] :=
  Module[{llv, lvb, clv, lvbs, erg},
   llv = Length[lv];
   Do[lvb = Select[innen, Not[FreeQ[#, lv[[ii]]]] &];
    clv[ii] = 1;
    If[lvb == True, clv[ii] = 0];
    If[((Head[lvb] === And) || (Head[lvb] === Or)), 
     clv[ii] = Length[lvb]], {ii, 1, llv}];
   lvb = Table[{lv[[ii]], clv[ii]}, {ii, 1, llv}];
   lvbs = Sort[lvb, #1[[2]] >= #2[[2]] &];
   erg = Table[lvbs[[ii, 1]], {ii, 1, llv}];
   ein[erg, innen]];
(* Analog zu allepos *)
lvi[ausdruck_] :=
    Module[{erg},
   erg = Replace[
     ausdruck, {alle[{nn__}, innen_] :>  alleimp[alle[{nn}, innen]], 
      ein[{nn__}, innen_] :> einimp[ein[{nn}, innen]]} , {0, 
      Infinity}];
      wf[erg]];
(*"lvi" = "Laufvariablenimplosion", Variablen einzelner Quantoren \
werden in eine Liste zusammengefasst.*)
litexp[kk_[ll__]] := 
    If[(Union[ Map[Head, {ll}]] === {Integer}), 
      indicesToOriginalLevel[kk[ll]], kk[ll]];
(*"litexp" bringt Indices von Variablen in die Standardform.
Beispiel: x[1,2,3] -> x[1][2][3].*)
lve[ausdruck_] :=
    Module[{erg},
   erg = Replace[
     ausdruck, {alle[{nn__ /; (Length[{nn}] > 1)}, innen_] :> 
       alleexp[alle[{nn}, innen]], 
      ein[{nn__ /; (Length[{nn}] > 1)}, innen_] :>  
       einexp[ein[{nn}, innen]]}, {0, Infinity}];
   erg = Replace[erg, 
     x_[indizes__] :>  litexp[x[indizes]], {0, Infinity} ];
      wf[erg]];
(*"lve" = "Laufvariablenexplosion". Die Variable in einer Liste \
werden auf die Quantoren verteilt.*)
lvp[ausdruck_] :=
    Module[{erg},
   erg = Replace[
     ausdruck, {alle[{nn__ /; (Length[{nn}] > 1)}, innen_]  :>  
       allepos[alle[{nn}, innen]], 
      ein[{nn__ /; (Length[{nn}] > 1)}, innen_] :>  
       einpos[ein[{nn}, innen]]}, {0, Infinity}];
      wf[erg]];
(*"lvp" =  Im input werden alle Quantoren mit mehr als einer \
Laufvariablen gefunden und diese Laufvariablen werden nach der Anzahl \
ihrer Auftritte in den verschiedenen Teilausdrücken des inputs \
sortiert. Z.B. in einem input mit nur zwei Teilausdrücken wird eine \
Laufvariable, die je einmal in jedem der Teilausdrücke auftaucht,in \
der Sortierung bevorzugt vor einer Laufvariablen, die sagen wir \
zehnmal, aber in nur einem der Teilausdrücke auftaucht *) 

(*A2. PN-BEFEHLE*)

(*Die folgenden Befehle implementieren die pn-Gesetze, so dass der \
Wirkungsbereich der Quantoren, wenn möglich, minimiert wird.*)
(*PN3*)pn3[list_] :=
  Module[{qlist, erg},
   qlist = lve[lvp[lvi[list]]];
   erg = qlist;
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[alle[{nn_}, innen_Or], 
        alle[{nn}, Select[innen, Not[unabhaengigQ[#, {nn}]] &]] \[Or] 
         Select[innen, unabhaengigQ[#, {nn}] &]]] &, erg];
   If[erg =!= qlist, Return[wf[lve[erg]]]];
   list];
(*PN5*)pn5[list_] :=
  Module[{qlist, erg},
   qlist = lve[lvp[lvi[list]]];
   erg = qlist;
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[ein[{nn_}, innen_And], 
        ein[{nn}, Select[innen, Not[unabhaengigQ[#, {nn}]] &]] && 
         Select[innen, unabhaengigQ[#, {nn}] &]]] &, erg];
   If[erg =!= qlist, Return[wf[lve[erg]]]];
   list];
(*PN9*)pn9[list_] :=
  Module[{qlist, erg},
   qlist = lve[lvp[lvi[list]]];
   erg = qlist;
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[alle[{nn_}, innen_And], 
        Map[alle[{nn}, #] &, innen]]] &, erg];
   If[erg =!= qlist, Return[wf[lve[erg]]]];
   list];
(*PN10*)pn10[list_] :=
  Module[{qlist, erg},
   qlist = lve[lvp[lvi[list]]];
   erg = qlist;
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[ein[{nn_}, innen_Or], 
        Map[ein[{nn}, #] &, innen]]] &, erg];
   If[erg =!= qlist, Return[wf[lve[erg]]]];
   list];

(*A3. PN*)
apn[ausdruck_] :=
  Module[{erg},
   erg = ausdruck;
   erg = pn9[ausdruck];
   If[(erg =!= ausdruck), ZPrint[" PN9 : ", tradi[lve[erg]]][5]; 
    Return[wf[erg]]];
   erg = pn10[ausdruck];
   If[(erg =!= ausdruck), ZPrint[" PN10 : ", tradi[lve[erg]]][5]; 
    Return[wf[erg]]] ;
   erg = pn5[ausdruck];
   If[(erg =!= ausdruck), ZPrint[" PN5 : ", tradi[lve[erg]]][5]; 
    Return[wf[erg]]];
   erg = pn3[ausdruck];
   If[(erg =!= ausdruck), ZPrint[" PN3/PN4 : ", tradi[lve[erg]]][5]; 
    Return[wf[erg]]];
   ausdruck]; 
pn[ausdruck_] := FixedPoint[apn, ausdruck];
(* Die pn-Regeln werden solange angewendet bis sich nichts mehr \
verändert.*)

(*B. LE*)
InnerhalbAlleCNF[list_] :=
  Module[{erg},
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[alle[{nn__}, innen_], 
        alle[{nn}, BooleanMinimize[innen, "CNF"]]]] &, list];
   ZPrint["scope of universal quantifiers converted to CNF: ", 
     tradi[erg]][5];
   erg];
InnerhalbEinDNF[list_] :=
  Module[{erg},
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[ein[{nn__}, innen_], 
        ein[{nn}, BooleanMinimize[innen, "DNF"]]]] &, list];
   ZPrint["scope of existential quantifiers converted to DNF: ", 
     tradi[erg]][5];
   erg];
(*Diese Befehle sichern die maximale Anwendbarkeit von PN9 und PN10.*)

JunctorSimplify[aa_ /; Head[aa] =!= List] := 
  Simplify[LogicalExpand[aa]];
(* Dieser Befehl wird zur Zeit nicht verwendet, könnte aber nützlich \
sein. Er vereinfacht aussagenlogische Ausdrücke. Das kann u.U. auch \
für scopes von Quantoren Anwendung finden: \
alle[{x},JunctorSimplify[Implies[f[x],p]]] würde ganz
richtig in alle[{x},p||!f[x]] umgeformt. Durch die Regeln alle[{x__}, \
etwas_] -> alle[[x},JunctorSimplify[etwas]] und ein[{x__}, etwas_] -> \
ein[{x}, JunctorSimplify[etwas]] kann der Befehl sinnvolle Anwendung \
im Logikprogramm finden.*)

QuantorSimplifyCore[list_] :=
  Module[{tm},
   tm = list;
   tm = pn[tm];
   tm = InnerhalbAlleCNF[tm];
   tm = pn[tm];
   tm = InnerhalbEinDNF[tm];
   tm = pn[tm];
   tm];
(*Dieser Befehl definiert die Abfolge der Teilbefehle, die dann in le \
durch den FixedPointbefehl iteriert werden bis sich nichts mehr \
ändert.*)

(*IP3\[And]*)
(* In den folgenden beiden Regeln habe ich entgegen der Empfehlung \
Leonid Shifrins, der Mma Version 6 benutzt hat, die Benutzung von \
MapAll[ReplaceRepeated[... einfach durch ReplaceRepeated ersetzt. \
Alle Beispiele verliefen korrekt, und ich bin überzeugt,
daß ab Verson 7 die Funktion ReplaceRepeated tatsächlich auf allen \
Leveln eines Ausdrucks ersetzt *)
ip3and[expression_] :=
  Module[{expr1, expr2},
   expr1 = lvi[expression];
   (*Wir müssen hier die implodierten Formen verwenden, 
   denn sonst können wir ip3and nicht anwenden, 
   wenn mehrere Existenzquantoren aufeinander in anderer Reihenfolge \
auftreten.*)
   expr2 = 
    ReplaceRepeated[expr1, 
     RuleDelayed[(oo___ && ein[{yy1__}, ll1_And] && 
         ein[{yy2__}, ll2_]) /; (SubsetQ[{yy2}, {yy1}] && 
         SubsetQ[{ll2}, listenform[ll1]]), 
      ein[Sort[{yy1}], ll1] && oo]];
   If[expr2 =!= expr1, 
    ZPrint["expression simplified by IP3a: ", tradi[expr2]][4];
    Return[wf[lve[expr2]]]]; expression];

(*IP2\[Or]*)
ip2or[expression_] :=
  Module[{expr1, expr2},
   expr1 = lvi[expression];
   expr2 = 
    ReplaceRepeated[expr1, 
     RuleDelayed[((aa___ && alle[{xx1__}, ll1_Or]) \[Or] (aa___ && 
           alle[{xx2__}, ll2_])) /; (SubsetQ[{xx2}, {xx1}] && 
         SubsetQ[{ll2}, listenform[ll1]]), 
      alle[Sort[{xx1}], ll1] && aa]];
   If[expr2 =!= expr1, 
    ZPrint["expression simplified by IP2or: ", tradi[expr2]][4];
    Return[wf[lve[expr2]]]]; expression];

simple[expression_] :=
  Module[{expr},
   expr = minIndizierung[expression];
   expr = ip3and[expr];
   expr = ip2or[expr];
   expr = Simplify[expr];
   If[expr =!= expression, 
    ZPrint["expression simplified by simple: ", tradi[expr]][4]];
   expr];
(*"simple" vereinfacht Ausdrücke. Es gibt minindizierte Ausdrücke aus \
(Vorsicht bei FixedPointbefehlen!)*)

 le[xx_ /; (Head[xx] =!= List) && (Not[FreeQ[xx, alle]] || 
       Not[FreeQ[xx, ein]])] :=
  Module[{tm},
   tm = simple[xx];
   ZPrint["Simplification within le: ", tradi[tm]][5];
   tm = FixedPoint[QuantorSimplifyCore, tm];
   tm = simple[tm];
   ZPrint["result of le: ", tradi[tm]][4];
   tm];
(*Dies ist der eigentliche le Befehl für quantorenlogische Formeln.*)

le[xx_ /; (Head[xx] =!= List) && (FreeQ[xx, alle] && 
       FreeQ[xx, ein])] :=
  Module[{erg},
   erg = Simplify[xx]; erg];
(*Der le Befehl für aussagenlogische Formeln reduziert sich auf den \
Mathematica Befehl Simplify.*)

(*Zu Simplify und BooleanMinimize: Es ist zu beachten, dass Simplify \
besser zur Vereinfachung von quantorenlogischen Formeln geeignet ist,
während BooleanMinimze der bessere Befehl ist, um nach \
aussagenlogischen Kriterien optimierte DNF zu erhalten. 
Zu Simplify und FullSimplify: Für logische Vereinfachungen reicht es, \
sich auf Simplify zu beschränken.*)


(*STANDARDIZATION (besser wäre "optimizer")*)
(*Dieses Modul standardisiert und optimiert im Rahmen des Algorithmus \
logische Ausdrücke. Hierbei kann vorausgesetzt werden, dass die \
Laufvariablen in explodierter Form vorliegen, die allquantifizierten \
Variablen x-Variable sind und die existenzquantifizerten Variablen \
y-Variablen sind sowie die Ausdrücke in expandierter Form vorliegen.
Dies wird am Anfang von decide sicher gestellt und bleibt während der \
Iteration erhalten.
Die Standardisierung sieht folgende Schritte vor:
  1. Umformung in optimierte DNFFOL mittels. Dies impliziert mit \
Simplify Identifikation expliziter Widersprüche als "False". 
2. Identifikation expliziter sat-Ausdrücke mittels satDisjunktion. \
Dies führt u.U. zu weiteren Vereinfachungen.

Die Optimierungen in 1. werden durch sukzessive Umformungen von \
invexer Form in pränexe Formen, wobei jeweils getestet wird, ob die \
Anwendungsbedingungen von Simplify sowie ip3and und ip2or erfüllt \
sind, um maximal nach diesen Gesetzen vereinfachen zu können. Am Ende \
wird dann in eine disjunktive Normalform umgeformt, in denen die \
Wirkungsbereiche der Quantoren maximal minimiert ist.*)


(*invpn5b*)
invpn5b[expression_] :=
  Module[{standard, expr},
   standard = lve[lvp[lvi[expression]]];
   expr = standard;
   expr = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[
        oo___ && ein[{yy1_}, 
          innen1_] && (konj2_ /; Head[konj2] =!= ein), 
        ein[{yy1}, innen1 && konj2] && oo]] &, expr];
   If[expr =!= standard, Return[wf[lve[expr]]]];
   expression];
(*invpn5b zieht Existenzquantoren in Konjunkten nur vor, wenn das \
andere Konjunkt keinen Quantor als Kopf hat. *)

(*invpn3b*)
invpn3b[expression_] :=
  Module[{standard, expr},
   standard = lve[lvp[lvi[expression]]];
   expr = standard;
   expr = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[
        oo___ || alle[{xx1_}, 
          innen1_] || (disj2_ /; Head[disj2] =!= alle),  
        alle[{xx1}, innen1 || disj2] || oo]] &, expr];
   If[expr =!= standard, Return[wf[lve[expr]]]];
   expression];
(*invpn3b zieht Allquantoren in Disjunkten nur vor, wenn das andere \
Disjunkt keinen Quantor als Kopf hat.*)

(*invpn1b*)
invpn1b[expression_] :=
  Module[{standard, expr},
   standard = lve[lvp[lvi[expression]]];
   expr = standard;
   expr = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[
        oo___ && alle[{xx1_}, 
          innen1_] && (konj2_ /; (Head[konj2] =!= alle)), 
        alle[{xx1}, innen1 && konj2] && oo]] &, expr];
   If[expr =!= standard, Return[wf[lve[expr]]]];
   expression];
(*invpn1b zieht Allquantoren in Konjunkten nur vor, wenn das andere \
Konjunkt keinen Quantor als Kopf hat.*)

(*invpn7b*)
invpn7b[expression_] :=
  Module[{standard, expr},
   standard = lve[lvp[lvi[expression]]];
   expr = standard;
   expr = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[
        oo___ || ein[{yy1_}, 
          innen1_] || (disj2_ /; Head[disj2] =!= ein),  
        ein[{yy1}, innen1 || disj2] || oo]] &, expr];
   If[expr =!= standard, Return[wf[lve[expr]]]];
   expression];
(*invpn7b zieht Existenzquantoren in Disjunkten nur vor, wenn das \
andere Disjunkt keinen Quantor als Kopf hat.*)

(*invPN9*)
invpn9[expression_] :=
  Module[{standard, expr},
   standard = lve[lvp[lvi[expression]]];
   expr = standard;
   expr = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[
        oo___ && alle[{xx1_}, innen1_] && alle[{xx2_}, innen2_ ],  
        alle[{xx1}, innen1 && (innen2 /. xx2 -> xx1)] && oo]] &, expr];
   If[expr =!= standard, Return[wf[lve[expr]]]];
   expression];
(*invPN9 kehrt PN9 um. Es wird verwendet um pränexe Normalformen zu \
bilden, in denen allquantifizierte Variable möglichst identisch sind.*)

(*invPN10*)
invpn10[expression_] :=
  Module[{standard, expr},
   standard = lve[lvp[lvi[expression]]];
   expr = standard;
   expr = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[
        oo___ || ein[{xx1_}, innen1_] || ein[{xx2_}, innen2_ ], 
        ein[{xx1}, innen1 || (innen2 /. xx2 -> xx1)] || oo]] &, expr];
   If[expr =!= standard, Return[wf[lve[expr]]]];
   expression];
(*invPN10 kehrt PN10 um. Es wird verwendet um pränexe Normalformen zu \
bilden, in denen existenzquantifizierte Variable möglichst identisch \
sind.*)

(*invPN5*)
invpn5[expression_] :=
  Module[{standard, expr},
   standard = lve[lvp[lvi[expression]]];
   expr = standard;
   expr = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[oo___ && ein[{yy1_}, innen1_] && konj2_ein,   
        ein[{yy1}, innen1 && konj2] && oo]] &, expr];
   If[expr =!= standard, Return[wf[lve[expr]]]];
   expression];
(*invPN5 kehrt PN5 um.*)

(*invPN3*)
invpn3[expression_] :=
  Module[{standard, expr},
   standard = lve[lvp[lvi[expression]]];
   expr = standard;
   expr = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[oo___ || alle[{xx1_}, innen1_] || disj2_alle, 
        alle[{xx1}, innen1 || disj2] || oo]] &, expr];
   If[expr =!= standard, Return[wf[lve[expr]]]];
   expression];
(*invPN3 kehrt PN3 um.*)

ainvpn[expression_] :=
  Module[{expr1, expr2},
   expr2 = wf[simple[expression]];
   expr2 = maxIndizierung[expr2];
   (*Die folgenden invertierten pn-
   Befehle setzen maxIndizierung voraus, da sonst nicht-
   wohlgeformte Formeln entstehen. 
   Es muss an dieser Stelle ergs neu definiert werden, 
   damit FixedPoint nicht in eine Schleife gerät, 
   in der in simple minIndizierung angewendet wird und in den \
invertierten pn-Gesetzen maxIndizierung.*)
   expr1 = invpn5b[expr2];
   If[expr1 =!= expr2, ZPrint["invpn5b applied: ", tradi[expr1]][4]; 
    Return[expr1]];
   expr1 = invpn3b[expr1];
   If[expr1 =!= expr2, ZPrint["invpn3b applied: ", tradi[expr1]][4]; 
    Return[expr1]];
   expr1 = invpn9[expr1];
   If[expr1 =!= expr2, ZPrint["invpn9 applied: ", tradi[expr1]][4]; 
    Return[expr1]];
   expr1 = invpn10[expr1];
   If[expr1 =!= expr2, ZPrint["invpn10 applied: ", tradi[expr1]][4]; 
    Return[expr1]];
   expr1 = invpn1b[expr1];
   If[expr1 =!= expr2, ZPrint["invpn1b applied: ", tradi[expr1]][4]; 
    Return[expr1]];
   expr1 = invpn7b[expr1];
   If[expr1 =!= expr2, ZPrint["invpn7b applied: ", tradi[expr1]][4]; 
    Return[expr1]];
   expr1 = invpn5[expr1];
   If[expr1 =!= expr2, ZPrint["invpn5 applied: ", tradi[expr1]][4]; 
    Return[expr1]];
   expr1 = invpn3[expr1];
   If[expr1 =!= expr2, ZPrint["invpn3 applied: ", tradi[expr1]][4]; 
    Return[expr1]];
   expr1]; 
(*ainvpn formt sukzessive in pränexe Normalformen um, und erhöht \
damit Schritt für Schritt die Anwendungsmöglickeiten von simple. Die \
Reihenfolge der Befehle darf nicht verändert werden.*)

standardization[expression_] :=
  Module[{expr},
   (*T.L. Bin nicht sicher, 
   ob hier nicht doch le vorgeschaltet werden muss. 
   Vielleicht auch nur einmal in decide.*)
   expr = simple[expression];
   expr = pn[expr];
   ZPrint["invex form: ", tradi[expr]][4];
   expr = FixedPoint[ainvpn, expr];
   ZPrint["optimized prenex normal form: ", tradi[expr]][4]; 
   expr = le[expr];
   expr = maxIndizierung[expr];
   expr = satDisjunktion[expr];
   expr]; 

(*qe *)
(*"qe" steht für "quantifier-elimination. Der Behlehl qe bildet das \
Herz des Algorithmus - durch ihn werden Allquantoren eliminiert.*)

(*T.L.8: AB HIER NUR NOCH UNVOLLSTÄNDIGE ERKLÄRUNGEN.*)

(*A. HILFSBEFEHLE FÜR qe*)

aekombis[list1_, list2_] := 
  Module[{ergstart, erg, lae1, lae2, lae, startpos, akt, aktneu, 
    neupos, ind},
   If[(list1 === {}) && (list2 === {}), Return[{}]];
   If[list1 === {}, Return[{list2}]];
   If[list2 === {}, Return[{list1}]];
   lae1 = Length[list1]; lae2 = Length[list2]; lae = lae1 + lae2; 
   ergstart = Table[xd, {lae}]; erg = {};
   If[lae1  <= lae2,  
    startpos = Table[{jj}, {jj, 1, lae - lae1 + 1}];
    neupos = startpos;
    Do[Do[akt = startpos[[jj]]; 
      aktneu = 
       Table[Append[akt, kk], {kk, Last[akt] + 1, lae - lae1 + var}];
      neupos[[jj]] = aktneu, {jj, 1, Length[startpos]}];
     neupos = Flatten[neupos, 1]; startpos = neupos, {var, 2, lae1}];
    Do[aktneu = ergstart; akt = neupos[[ii]]; 
     Do[aktneu[[akt[[jj]] ]] = list1[[jj]], {jj, 1, lae1}];
     ind = 0; aktneu = aktneu //. xd :> list2[[++ind]];
     erg = Append[erg, aktneu], {ii, 1, Length[neupos]}],
    startpos = Table[{jj}, {jj, 1, lae - lae2 + 1}];
    neupos = startpos;
    Do[Do[akt = startpos[[jj]]; 
      aktneu = 
       Table[Append[akt, kk], {kk, Last[akt] + 1, lae - lae2 + var}];
      neupos[[jj]] = aktneu, {jj, 1, Length[startpos]}];
     neupos = Flatten[neupos, 1]; startpos = neupos, {var, 2, lae2}];
    Do[aktneu = ergstart; akt = neupos[[ii]]; 
     Do[aktneu[[akt[[jj]] ]] = list2[[jj]], {jj, 1, lae2}];
     ind = 0; aktneu = aktneu //. xd :> list1[[++ind]];
     erg = Append[erg, aktneu], {ii, 1, Length[neupos]}]];
   erg];
(*"aekombis" bildet Kombinationation aus zwei Listen. In pnrSInnen \
dient der Befehl dazu, alle Quantorenketten gebildet, in denen \
Existenzquantoren möglichst vor Allquantoren stehen, wobei jedoch die \
relative Reihenfolge all- und existenzquantifizierter Variablen der \
jeweiligen Listen erhalten bleiben muss. *)
step13a[ausdruck_, zuEliminieren_] :=
  Module[{erg, lae},
   erg = ausdruck;
   lae = Length[zuEliminieren];
   Do[erg = 
     MapAll[ReplaceAll[#, 
        RuleDelayed[ein[{zuEliminieren[[jj]]}, rest1_], rest1]] &, 
      erg];
    erg = 
     MapAll[ReplaceAll[#, 
        RuleDelayed[alle[{zuEliminieren[[jj]]}, rest2_], rest2]] &, 
      erg], {jj, 1, lae}];
   erg];
(* Die Funktion step13a eliminiert in pnrSInnen die Quantoren der \
jeweiligen Liste NEJAMNEJEKOMBI aus dem ursprünglichen Ausdruck, \
damit dann in step13b die Quantorenkette NEJAMNEJEKOMBI vor den \
Junktor im ursprünglichen Ausdruck plaziert werden kann.*)
ersterBuchstabe[lv_] := First[Take[FixedPointList[Head, lv], -3]];
(* Der erste Buchstabe einer indizierten Varablen läßt sich nicht \
trivial mit Head finden, z.B. ist Head[x[1][2][3]] gleich x[1][2].
Man muß die FixedPont-Liste der Köpfe von Köpfen nehmen, die stets \
mit {..., erster Buchstabe der Laufvariable, Symbol, Symbol} endet,
d.h. die drittletzte Position ist der gesuchte erste Buchstabe.
"-3" erklärt sich daraus, dass genaugenommen geprüft wird, ob der \
drittletzte Kopf "x" ist, der vorletzte und letzte sind gemäß 
Mathematica "symbol". Die Vereinigung aller drittletzten Heads muss x \
ergeben. Dieser Befehl ist so kompliziert, da die x-Variablen \
beliebig indiziert sein können. *)
quantorisierung[{lv_ } /; (lv === x) || (ersterBuchstabe[lv] === x), 
   ausdruck_] := alle[{lv}, ausdruck];
quantorisierung[{lv_} /; (lv === y) || (ersterBuchstabe[lv] === y), 
   ausdruck_] := ein[{lv}, ausdruck];
step13b[qlist_ /; (Length[qlist] > 0), ausdruck_] := 
  Fold[quantorisierung[{#2}, #1] &, ausdruck, Reverse[qlist]];
(* step13b nimmt in pnrSInnen die jeweiligen NEJAMNEJEKOMBIs als \
Argument qlist und stellt sie jeweils dem Ausdruck schritt13a voran, \
d.i. step13ausdruck (= der Teilausdruck, dessen Kopf der selektierte \
Junktor ist) ohne die Quantoren der jeweiligen NEJEJAMNEJEKOMBIs.*)

xListeQ[{xe__}] := Union[Map[ersterBuchstabe[#] &, {xe}]] === {x};
(* "xListeQ" fragt, ob jedes Element einer Liste mit der Variablen x \
anfängt. *)
yListeQ[{ys__}] := Union[Map[ersterBuchstabe[#] &, {ys}]] === {y};
(*Analgo zu xListeQ.*)
pnrwfQ[{ausdruck_, {}, {}}] := True;
pnrwfQ[{ausdruck_, {xe__}, {ys__}}] :=
  xListeQ[{xe}] && yListeQ[{ys}];
(*pnrwfQ fragt, ob eine Liste bestehend aus ausdruck und zwei Listen, \
eine x- und y-Liste enthält. pnrwfQ gibt auch "True" aus, wenn die \
beiden Listen leer sind.*)
allquantorvermehrer[alle[{li_}, innen_], wieoft_] := 
  Apply[And, 
   Table[alle[{li[ii]}, (innen /. li -> li[ii])], {ii, 1, wieoft}]];
allquantorvermehrer[alle[{li_[ind__]}, innen_], wieoft_] := 
  Apply[And, 
   Table[alle[{li[ind, ii]}, (innen /. li[ind] -> li[ind, ii])], {ii, 
     1, wieoft}]];

(*B. STEP 1 of qe*)
xidpairs[{lit1_ , Not[lit2_]}] := 
  Module[{erg},
   erg = {};
   Do[If[ersterBuchstabe[lit1[[ii]]] === x && 
      ersterBuchstabe[lit2[[ii]]] === x && lit1[[ii]] =!= lit2[[ii]],
     erg = Append[erg, {lit1[[ii]], lit2[[ii]]}]], {ii, 1, 
     Length[lit1]}];
   ZPrint["x-idpairs within one K-pair: ", erg][5];
   erg];
(*xidpairs gibt Paare von x-Variablen aus, die an identischen \
Argumentstellen eines K-paares vorkommen.*)
xpairs[xidpairs_] :=
  Module[{xvar, xclass, akt1, erg, xflat, newxclass},
   xvar = DeleteDuplicates[Cases[xidpairs, x[_], {0, Infinity}]];
   ZPrint["x-variables within x-idpairs: ", xvar][5];
   erg = {};
   Do[akt1 = xvar[[ii]];
    xclass = 
     DeleteDuplicates[
      Cases[xidpairs, 
       partialexpression_ /; 
        Head[partialexpression] === List && 
         MemberQ[partialexpression, xvar[[ii]]], {0, Infinity}]];
    ZPrint["x-idpairs with ", akt1, " as constant element: ", xclass][
     5]; 
    xflat = Union[Flatten[xclass]];
     ZPrint["x-variables connected with ", akt1, " : ", xflat][5]; 
    newxclass = Subsets[xflat, {2}]; 
    ZPrint["new list of x-pairs: ", newxclass][5];
    erg = Append[erg, newxclass], {ii, 1, Length[xvar]}]; 
   ZPrint["unflatted list of x-pairlists with duplicates: ", erg][5]; 
   erg = DeleteDuplicates[Flatten[erg, 1]]; 
   ZPrint["flatted list of all x-pairs without duplicates: ", erg][5];
   erg];
(*xpairs bestimmt aus xidpairs alle x-Paare (also auch die, die auf \
"Transitivität" beruhen). Dies wird durch die Bildung jeweils aller \
subsets zu jeder Liste von Paaren, denen eine x-Variable gemeinsam \
ist, erreicht.)*)
 yklist[{poslit_, Not[neglit_]}, sxlist_, expression_] :=
  Module[{erg, akt1, akt2},
   erg = {};
   Do[akt1 = poslit[[ii]]; akt2 = neglit[[ii]]; 
    If[(MemberQ[sxlist, akt1, Infinity] && 
       ersterBuchstabe[akt2] === y && FreeQ[expression, {akt2}]), 
     erg = Append[erg, akt2]]; 
    If[ersterBuchstabe[akt1] === y && FreeQ[expression, {akt1}] && 
      MemberQ[sxlist, akt2, Infinity], erg = Append[erg, akt1]], {ii, 
     1, Length[poslit]}];
   erg = DeleteDuplicates[erg];
   erg]; 
(*yklist gibt für ein gegebenes K-pair, eine selected xListe und \
einen Ausdruck (nämlich dem, dem der zu eliminierende Allquantor \
voransteht) die Liste an y-Variablen aus, die an identischen \
Argumentstelle mit Variablen der selected x-Liste vorkommen.*)
ylist[kpairlist_, sxlist_, expression_] :=
  Module[{akt, erg, ylist},
   erg = {};
   Do[akt = kpairlist[[ii]]; ylist = yklist[akt, sxlist, expression]; 
    erg = Append[erg, ylist], {ii, 1, Length[kpairlist]}];
   erg = Union[Flatten[erg]];
   ZPrint["y-list identified by k-pairs: ", erg][4];
   erg];
(*ylist gibt für eine gegebene Liste von K-Paaren, eine gegebene \
Liste von x-Paaren und einen Ausdruck (nämlich dem, dem der zu \
eliminierende Allquantor voransteht) eine y-Liste aus. Es verwendet \
dabei das Modul yklist.*)
ynotinscope[expression_] := 
  Flatten[Cases[
    expression, {y[no_]} /; 
     FreeQ[expression, 
      alle[{lv_}, scope_ /; Not[FreeQ[scope, {y[no]}]]]], {0, 
     Infinity}]];
qe1Simple[expression_] :=
  Module[{exp1, lae, pos, erg, selectedall, selectedxvar, sylist, 
    yvarimScope, multiplied, multipliedxvar, ls, lesy, kpairlist, 
    xidpairlist, xpairlist, xselected, xvar1, xvar2, yvar1, yvar2, 
    sxlist, ynotscope, yint, yvarnotinscope},
   exp1 = lve[expression];
   pos = Position[exp1, alle];
   pos = Last[pos];
   lae = Length[pos];
   pos = ReplacePart[pos, lae -> 1];
   erg = First[exp1[[pos /. List -> Sequence]]];
   pos = erg;
   selectedall = 
    First[Cases[exp1, alle[{pos}, innen2_], {0, Infinity}]];
   ZPrint["selected universal quantifier with scope: ", selectedall][
    5];
   (* Soweit das alte qe2Single. Im Folgenden soll die y-
   Liste nach strengeren Kriterien bestimmt werden.*)
   selectedxvar = selectedall[[1, 1]];
   ZPrint["variable of universal quantifier to be eliminated: ", 
     selectedxvar][3];
   kpairlist = kpairs[expression];
   xidpairlist = Flatten[Map[xidpairs, kpairlist], 1];
   ZPrint["All x-idpairs at identical positions: ", xidpairlist][4];
   xpairlist = xpairs[xidpairlist];
   xselected = 
    Cases[xpairlist, 
     partialexpression_ /; 
      Head[partialexpression] === List && 
       MemberQ[partialexpression, selectedxvar], {0, Infinity}];
   ZPrint["selected x-pairs, in which ", selectedxvar , 
     " is a member: ", xselected][4];
   sxlist = DeleteDuplicates[Flatten[xselected]];
   If[sxlist === {}, sxlist = {selectedxvar}, sxlist];
   ZPrint["selected list of x-variables: ", sxlist][4];
   sylist = ylist[kpairlist, sxlist, selectedall];
   (*Das Folgende an Stelle von bb.*)
   ynotscope = ynotinscope[expression];
   If[((sxlist =!= {selectedxvar}) || (sylist === {} && 
        sxlist === {selectedxvar})),
    If[ynotscope === {}, sylist = Prepend[sylist, y[0]], 
     yint = Intersection[ynotscope, sylist];
     If[yint === {}, sylist = Prepend[sylist, First[ynotscope]]]]];
   ZPrint["y-list =", tradi[sylist]][4];
   (*Ab hier wieder das alte qe2Single.*)
   lesy = Length[sylist];
   ZPrint["number m of elements in the y list = ", lesy][4];
   ZPrint["So the selected expression part should be multiplicated ", 
     lesy - 1, " times "][4];
   If[lesy > 1, multiplied = allquantorvermehrer[selectedall, lesy], 
    multiplied = selectedall];
   ZPrint["multiplied selected expression: ", tradi[multiplied ]][4];
   erg = lve[(exp1 /. selectedall -> multiplied)];
   If[lesy > 1, multipliedxvar = Table[pos[ii], {ii, 1, lesy}], 
    multipliedxvar = {pos}];
   ZPrint["x-list: ", tradi[multipliedxvar]][4];
   ZPrint["result of 1st step of qe (expression, x-, y-list): ", 
     tradi[{erg, multipliedxvar, sylist}]][3];
   {erg, multipliedxvar, sylist}];

(*C. STEP 2 of qe*)
pnrSInnen[q2output_] :=
  Module[{zuElAll, mm, ii, akt, q2o, ergq2, selectedEin, 
    selectedEinLV, mglJ, step3preparation, kopfstep3, hilfsm, selhilf,
     step3ausdruck, step3J, step4JA, step5JAM, step6JE, step7NEJAM, 
    step8NEJE, step9ONEJAM, step9ONEJE, splittedONEJAM, doppelteAnz, 
    splittedONEJE, step10ONEJAM, step10ONEJE, step10m, step10n, 
    ONEJAM, ONEJE, allekombis, step11kombis, AEKOMBI, posSelEin, 
    step11k, NEJAMNEJEKOMBI, schritt13a, schritt13b, out, lle, erg}, 
   Off[First::first, Part::partw];
   ZPrint["input of 2nd step of qe: ", tradi[q2output]][4];
   q2o = lve[q2output];
   q2o = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[alle[{lv_}, innen_], 
        alle[{lv}, innen] /. lv -> indicesToSameLevel[lv]]] &, q2o];
   q2o = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[ein[{lv_}, innen_], 
        ein[{lv}, innen] /. lv -> indicesToSameLevel[lv]]] &, q2o];
   q2o[[2]] = Map[indicesToSameLevel, q2o[[2]]];
   q2o[[3]] = Map[indicesToSameLevel, q2o[[3]]];
   ergq2 = q2o[[1]];
   zuElAll = First[q2o[[2]]] /. First[{}] -> {};
   If[pnrflag == False, 
    If[zuElAll =!= {}, 
     ZPrint["\[ForAll] quantifier to be eliminated:  \[ForAll]", 
       tradi[zuElAll]][4], 
     ZPrint["There exist no \[ForAll] quantifier which can be \
eliminated"][4]]];
   mm = Last[q2o][[1]];
   selectedEin = 
    First[Cases[ergq2, ein[{mm}, irgendwas_], {0, Infinity}]] /. 
     First[{}] -> {};
   selectedEinLV = First[First[selectedEin]] /. First[{}] -> {};
   If[pnrflag == False, 
    If[selectedEinLV =!= {}, 
     ZPrint["\[Exists] quantifier selected: \[Exists]", 
       tradi[selectedEinLV]][4], 
     ZPrint["\[Exists] quantifier selected: \[Exists]y\!\(\*
       StyleBox[\"0\",\nFontSize->10]\)"][4]]];
   If[Not[FreeQ[selectedEin, alle[{zuElAll}, etwas2_]]], 
    If[pnrflag == False, 
     ZPrint[" \[ForAll] quantifier to be eliminated is in the scope \
of the \[Exists] quantifier. "][4]];
    pnrflag = True;
    Return[{q2output}]];
   mglJ = 
    Cases[ergq2, 
     ausdruck_ /; ((Head[ausdruck] === And) || (Head[ausdruck] === 
           Or)) && (Not[
         FreeQ[ausdruck, alle[{zuElAll}, egal_]]]) && (Not[
         FreeQ[ausdruck, ein[{selectedEinLV}, egal2_]]]), {0, 
      Infinity}];
   ZPrint[
     "Selected conjunction / disjunction containing the selected \
\[Exists] quantifier and the \[ForAll] quantifier that is eliminated \
= ", tradi[mglJ]][4];
   step3preparation = First[mglJ] /. First[{}] -> {};
   kopfstep3 = Head[step3preparation];
   hilfsm = 
    Table[step3preparation[[ii]], {ii, 1, Length[step3preparation]}];
   selhilf = 
    Select[hilfsm, (Not[FreeQ[#, zuElAll]] || 
        Not[FreeQ[#, selectedEinLV]]) &];
   step3ausdruck = Apply[kopfstep3, selhilf];
   ZPrint[
     "Selected conjuncts / disjuncts containing the selected \
\[Exists] quantifier and the \[ForAll] quantifier that is eliminated \
= ", tradi[step3ausdruck]][4];
   step4JA = 
    First[Cases[step3ausdruck, 
      teilausdruck_ /; 
       Not[FreeQ[teilausdruck, alle[{zuElAll}, unterteilausdruck_]]]]];
   step4JA = 
    Cases[step4JA, 
     teilausdruck_ /; ((Head[teilausdruck] === alle || 
          Head[teilausdruck] === ein) && 
        Not[FreeQ[teilausdruck, 
          alle[{zuElAll}, unterteilausdruck_]]]), {0, Infinity}];
   step4JA = 
    Flatten[Reverse[
      Table[First[step4JA[[ii]]], {ii, 1, Length[step4JA]}]]];
   If[Length[step4JA] > 0, 
    step4JA = 
     Table[step4JA[[jj]], {jj, 1, 
       Position[step4JA, zuElAll][[1, 1]]}]];
   ZPrint["JA = ", step4JA][4];
   ii = Length[step4JA]; step5JAM = step4JA;
   While[ ersterBuchstabe[step5JAM[[ii]]] === x, 
    step5JAM = Delete[step5JAM, ii];
    ii = ii - 1];
   ZPrint["JAM =", step5JAM][4];
   step6JE = 
    First[Cases[step3ausdruck, 
      teilausdruck_ /; 
       Not[FreeQ[teilausdruck, 
         ein[{selectedEinLV}, unterteilausdruck_]]]]];
   step6JE = 
    Cases[step6JE, 
     teilausdruck_ /; ((Head[teilausdruck] === alle || 
          Head[teilausdruck] === ein) && 
        Not[FreeQ[teilausdruck, 
          ein[{selectedEinLV}, unterteilausdruck_]]]), {0, Infinity}];
   step6JE = 
    Flatten[Reverse[
      Table[First[step6JE[[ii]]], {ii, 1, Length[step6JE]}]]];
   If[Length[step6JE] > 0, 
    step6JE = 
     Table[step6JE[[jj]], {jj, 1, 
       Position[step6JE, selectedEinLV][[1, 1]]}]];
   ZPrint["JE =", step6JE][4];
   ii = 1; step9ONEJAM = step5JAM;
   Quiet[
    While[ersterBuchstabe[step9ONEJAM[[ii]]] === y, 
     step9ONEJAM = Delete[step9ONEJAM, ii]]];
   ZPrint["ONEJAM =", step9ONEJAM][4];
   ii = 1; step9ONEJE = step6JE;
   Quiet[
    While[ersterBuchstabe[step9ONEJE[[ii]]] === y, 
     step9ONEJE = Delete[step9ONEJE, ii]]];
   ZPrint["ONEJE =", step9ONEJE][4];
   step7NEJAM = Complement[step5JAM, step9ONEJAM];
   ZPrint["NEJAM =", step7NEJAM][4];
   step8NEJE = Complement[step6JE, step9ONEJE];
   ZPrint["NEJE =", step8NEJE][4];
   splittedONEJAM = 
    Split[step9ONEJAM, ersterBuchstabe[#1] === ersterBuchstabe[#2] &];
   doppelteAnz = Length[splittedONEJAM];
   step10m = Quotient[doppelteAnz, 2];
   ZPrint["m=", step10m][4];
   Do[ONEJAM[ii] = 
     Join[splittedONEJAM[[2*ii - 1]], splittedONEJAM[[2*ii]]];
    ZPrint["ONEJAM", ii, " = ", ONEJAM[ii]][4],
    {ii, 1, step10m}];
   splittedONEJE = 
    Split[step9ONEJE, ersterBuchstabe[#1] === ersterBuchstabe[#2] &];
   doppelteAnz = Length[splittedONEJE];
   step10n = Quotient[doppelteAnz, 2];
   ZPrint["n=", step10n][4];
   Do[ONEJE[ii] = 
     Join[splittedONEJE[[2*ii - 1]], splittedONEJE[[2*ii]]];
    ZPrint["ONEJE", ii, " = ", ONEJE[ii]][4],
    {ii, 1, step10n}];
   step11kombis = 
    aekombis[Table[ONEJAM[ii], {ii, 1, step10m}], 
     Table[ONEJE[jj], {jj, 1, step10n}]];
   step11k = Length[step11kombis];
   If[step11k == 0, AEKOMBI = {};
    ZPrint["AEKOMBI = {}"][4],
    Do[AEKOMBI[ii] = step11kombis[[ii]];
     posSelEin = First[First[Position[AEKOMBI[ii], selectedEinLV]]];
     AEKOMBI[ii] = Take[AEKOMBI[ii], posSelEin];
     (*Es werden die AEKOMBIS nur bis zum selektierten \
Existenzquantor genommen.*)
     ZPrint["AEKOMBI", ii, " = ", AEKOMBI[ii]][4], {ii, 1, step11k}]];
   If[step11k == 0, 
    NEJAMNEJEKOMBI[1] = Flatten[{step7NEJAM, step8NEJE, {}}];
    ZPrint["NEJAMNEJEKOMBI[1] = ", NEJAMNEJEKOMBI[1]][4], 
    Do[NEJAMNEJEKOMBI[ii] = 
      Flatten[{step7NEJAM, step8NEJE, AEKOMBI[ii]}];
     ZPrint["NEJAMNEJEKOMBI", ii, " = ", NEJAMNEJEKOMBI[ii]][4], {ii, 
      1, step11k}]];
   If[step11k == 0, 
    schritt13a[1] = step13a[step3ausdruck, NEJAMNEJEKOMBI[1]];
    ZPrint["output 1, 1st step within 2nd step of qe: ", 
      tradi[schritt13a[1]]][4], 
    Do[schritt13a[ii] = step13a[step3ausdruck, NEJAMNEJEKOMBI[ii]];
     ZPrint["output ", ii, " 1st step within 2nd step of qe: ", 
       tradi[schritt13a[ii]]][4],
     {ii, 1, step11k}]];
   If[step11k == 0, 
    schritt13b[1] = step13b[NEJAMNEJEKOMBI[1], schritt13a[1]];
    ZPrint["Output 1, 2nd step within 2nd step of qe: ", 
      tradi[schritt13b[1]]][4], 
    Do[schritt13b[ii] = step13b[NEJAMNEJEKOMBI[ii], schritt13a[ii]];
     ZPrint["Output ", ii, " 2nd step within 2nd step of qe: ", 
       tradi[schritt13b[ii]]][4],
     {ii, 1, step11k}]];
   If[step11k == 0, out[1] = ergq2 /. step3ausdruck -> schritt13b[1];
    ZPrint["Output 1, 3rd step within 2nd step of qe: ", 
      tradi[out[1]]][4], 
    Do[out[ii] = ergq2 /. step3ausdruck -> schritt13b[ii];
     ZPrint["Output ", ii, " 3rd step within 2nd step of qe: ", 
       tradi[out[ii]]][4], {ii, 1, step11k}]];
   If[step11k == 0, erg = {oo[out[1]], q2output[[2]], q2output[[3]]}, 
    erg = Table[{oo[out[ii]], q2output[[2]], q2output[[3]]}, {ii, 1, 
       step11k}]];
   (*"oo" kennzeichnet hier die outputs, um in der der Def. 
   von lle die Länge der outputs bestimmen zu können.*)
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[alle[{lv_}, innen_], 
        alle[{lv}, innen] /. lv -> indicesToOriginalLevel[lv]]] &, 
     erg];
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[ein[{lv_}, innen_], 
        ein[{lv}, innen] /. lv -> indicesToOriginalLevel[lv]]] &, erg];
   ZPrint[
     "Complete list of outputs marked as outputs and indices \
converted back to the original level: ", tradi[erg]][4];
   lle = Length[Cases[erg, oo[etwas__], {0, Infinity}]];
   If[(lle <= 1) && (Length[erg] == 3), erg = {erg}];
   On[First::first, Part::partw];
   (erg /. oo[etwas__] -> etwas)];
pnrS[{ausdruck_, {xl___}, {yl___}}] :=
  Module[{len, erg},
   len = Length[{xl}];
   pnrflag = False;
   erg = pnrSInnen[{ausdruck, {{xl}[[1]]}, {{yl}[[1]]}}];
   If[len > 1, 
    Do[erg = 
      MapAll[ReplaceAll[#, 
         RuleDelayed[{au_, xxl_, yyl_} /; 
           pnrwfQ[{au, xxl, yyl}], {au, {{xl}[[ii]]}, {{yl}[[
             ii]]}}]] &, erg];
     erg = Flatten[Map[pnrSInnen[#] &, erg], 1], {ii, 2, len}]];
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[{au_, xxl_, yyl_} /; 
         pnrwfQ[{au, xxl, yyl}], {au, {xl}, {yl}}]] &, erg];
   ZPrint[
     "result of 2nd step of qe (expression multiplied to create all \
necessary quantifier orders): ", erg][3]; 
   erg];

(*D. STEP 3 of qe*)
qe5SingleInput[{input_, {}, {}}] := {input, {}, {}};
qe5SingleInput[{input_, xl_, yl_} /; (Length[xl] > 0)] :=
  Module[{step2x1, step2y1, step4VorSubstitution, step4Substitution, 
    step4, neuexl, neueyl, step5le, erg},
   erg = {};
   step2x1 = xl[[1]]; 
   ZPrint["Selected universal x-variable (start of 3rd step of qe) = \
", tradi[step2x1]][4];
   step2y1 = yl[[1]]; 
   ZPrint["Selected existential y-variable = ", tradi[step2y1]][4];
   step4VorSubstitution = 
    Cases[input, alle[{step2x1}, irgendwas_], {0, Infinity}];
   ZPrint["before substitution: ", tradi[step4VorSubstitution]][4];
   step4Substitution = 
    Map[ReplaceAll[#[[2]], step2x1 -> step2y1] &, 
     step4VorSubstitution];
   ZPrint["substitution point: ", tradi[step4Substitution]][4];
   step4 = 
    input /. step4VorSubstitution[[1]] -> step4Substitution[[1]];
   ZPrint["step4: ", step4][4];
   If[FreeQ[step4, ein[{step2y1}, etwas_]], 
    step4 = ein[{step2y1}, step4]];
   ZPrint["after substitution: ", tradi[TableForm[step4]]][4];
   neuexl = DeleteCases[xl, step2x1];
   ZPrint["new x list = ", neuexl][4];
   neueyl = DeleteCases[yl, step2y1];
   ZPrint["new y list = ", neueyl][4];
   erg = Append[erg, {step4, neuexl, neueyl}];
   ZPrint["new expression: ", erg][4];
   erg[[1]]] ;
qe5[multiausdruck_] := 
  MapAll[ReplaceRepeated[#, 
     RuleDelayed[{au_, xl_, yl_} /; pnrwfQ[{au, xl, yl}], 
      qe5SingleInput[{au, xl, yl}]]] &,
   multiausdruck]; 

xyListenStreichen[multiausdruck_] := 
  MapAll[ReplaceAll[#, 
     RuleDelayed[{au_, xl_, yl_} /; pnrwfQ[{au, xl, yl}], au]] &, 
   multiausdruck];

 qe[ausdruck_ /; (Head[ausdruck] =!= Or)] :=
  Module[{erg, qe2Iter, pnrIter, qe5Iter, xyLS},
   erg = maxIndizierung[ausdruck];
   ZPrint["variables multiplied (preparing qe): ", tradi[erg]][4];
   qe2Iter = qe1Simple[erg];
   pnrIter = pnrS[qe2Iter];
   qe5Iter = qe5[pnrIter];
   ZPrint[
     "result of the completed substitution with empty x- and y-list: \
", qe5Iter][4];
   xyLS = xyListenStreichen[qe5Iter];
   ZPrint[
     "result of 3rd step of qe (elimination of the \[ForAll] \
quantifiers by substitution with the selected existential \
y-variable): ", xyLS][3];
   erg = Map[standardization, xyLS];
   erg = DeleteDuplicates[erg];
   ZPrint["duplicates deleted (tradi-output of qe): ", 
     tradi[TableForm[erg]]][3];
   erg = Map[List, erg];
   ZPrint[
     "qe-output as list of lists in order to identify partial \
expressions: ", erg][4];
   erg ];
qe[ausdruck_Or] := (undefined; 
   ZPrint["Head of input should not be Or"][3]); 

(*em *)

(* emSimplifying *)
emSimplifyingCore[
   expression_ /; (FreeQ[expression, 
      alle[{x_}, 
       scope1_ /; 
        Not[FreeQ[scope1, 
          ein[{y[no_]}, scope2_ /; (Head[scope2] === And)]]]]])] := 
  expression;
emSimplifyingCore[
   expression_ /; (Not[
      FreeQ[expression, 
       alle[{x_}, 
        scope1_ /; 
         Not[FreeQ[scope1, 
           ein[{y[no_]}, scope2_ /; (Head[scope2] === And)]]]]]])] :=  
  Module[{expr, kpairlist, sexpr1, tosubexpr, subexpr, akt1, akt2, 
    akt3, svar, subinstance, newsexpr1},
   expr = maxIndizierung[expression];
   ZPrint["expression with maximal indices: ", tradi[expr]][4];
   kpairlist = kpairs[expr];
   sexpr1 = 
    First[Sort[
      Cases[expr, 
       ein[{y[no_]}, scope2_] /; 
        Not[FreeQ[expr, 
          alle[{x_}, 
           scope1_ /; 
            Not[FreeQ[scope1, 
              ein[{y[no]}, scope2 /; (Head[scope2] === And)]]]]]], {0,
         Infinity}], LeafCount[#1] >=  LeafCount[#2] &]];
   ZPrint["selected partial expression: ", tradi[sexpr1]][4];  
   svar = First[Cases[sexpr1, y[no_], {0, Infinity}, 1]];
   ZPrint["selected y-variable: ", svar][4];
   tosubexpr = 
    Union[Cases[posList[sexpr1], 
      partialexpr1_ /; (LiteralQ[partialexpr1] && 
         MemberQ[partialexpr1, svar, Infinity] && 
         FreeQ[kpairlist, partialexpr1]), {0, Infinity}],
     Cases[negList[sexpr1], 
      Not[partialexpr2_] /; (LiteralQ[partialexpr2] && 
         MemberQ[partialexpr2, svar, Infinity] &&
         FreeQ[kpairlist, partialexpr2]), {0, Infinity}]];
   ZPrint["old literals: ", tradi[tosubexpr]][4];
   subexpr = {};
   Do[akt1 = tosubexpr[[ii]];
    subinstance = akt1 /. svar -> svar[ii];
    subexpr = Append[subexpr, subinstance], {ii, 1, 
     Length[tosubexpr]}];
   ZPrint["new literals: ", tradi[subexpr]][4];
   newsexpr1 = sexpr1;
   Do[akt2 = tosubexpr[[ii]];
    akt3 = subexpr[[ii]];
    newsexpr1 = newsexpr1 /. akt2 -> akt3;
    newsexpr1 = ein[{svar[ii]}, newsexpr1], {ii, 1, 
     Length[tosubexpr]}];
   newsexpr1 = wf[newsexpr1];
   ZPrint["new subexpression: ", tradi[newsexpr1]][4];
   expr = expr /. sexpr1 -> newsexpr1;
   ZPrint["new expression: ", tradi[expr]][4];
   expr = le[expr];
   ZPrint["new expression converted: ", tradi[expr]][4];
   expr];
emSimplifying[expression_] := 
  FixedPoint[emSimplifyingCore, expression];

(*A. HILFSBEFEHLE FÜR em*)
   KS = Compile[{{n, _Integer}, {k, _Integer}}, 
   Module[{h, ss = Range[k], x}, Table[(h = Length[ss]; x = n;
      While[x === ss[[h]], h--; x--];
      ss = 
       Join[Take[ss, h - 1], 
        Range[ss[[h]] + 1, ss[[h]] + Length[ss] - h + 1]]), {Binomial[
        n, k] - 1}]]];
    KSubsets[l_List, 0] := {{}};
    KSubsets[l_List, 1] := Partition[l, 1];
    KSubsets[l_List, 2] := 
  Flatten[Table[{l[[ii]], l[[jj]]}, {ii, Length[l] - 1}, {jj, ii + 1, 
     Length[l]}], 1];
    KSubsets[l_List, k_Integer?Positive] := {l} /; (k == Length[l]);
    KSubsets[l_List, k_Integer?Positive] := {} /; (k > Length[l]);
    KSubsets[s_List, k_Integer] := 
  Prepend[Map[s[[#]] &, KS[Length[s], k]], s[[Range[k]]]];
    listKomplement[l1_, l2_] :=
  Module[{aktl1, aktl2},
   aktl1 = l1;
   Do[aktl2 = l2[[ii]];
    aktl1 = DeleteCases[aktl1, aktl2, 1, 1], {ii, 1, Length[l2]}];
   aktl1];
  listeZweiteilen[ll_] :=
  Module[{lae, tl, t1, t2, erg = {}},
   lae = Length[ll];
   Do[tl = KSubsets[ll, ii];
    Do[t1 = tl[[jj]]; t2 = listKomplement[ll, t1];
     erg = Append[erg, Sort[{t2, t1}]], {jj, 1, Length[tl]}], {ii, 1, 
     Quotient[lae, 2]}];
   DeleteDuplicates[erg]];
myReplacer[{ausdruck1_, ausdruck2_}, my_] :=
  Module[{a1, a2, my1, my2},
   a1 = (ausdruck1 /. my -> my1);
   a2 = (ausdruck2 /. my -> my2);
   a1 = (a1 /. my1 -> my[1]);
   a2 = (a2 /. my2 -> my[2]);
   oo[a1, a2]];

(*STEP1 of em*)
emInnen[ein[{mu_}, konjunkte_] /; (Head[konjunkte] === And)] :=
  Module[{kl, alleK, kk, step3, step4},
   kl = listenform[konjunkte];
   alleK = listeZweiteilen[kl];
   ZPrint["result of 1st step of em (And-partitions): ", 
     tradi[alleK]][3];
   kk = Length[alleK];
   step3 = Map[myReplacer[{#[[1]], #[[2]]}, mu] &, alleK];
   ZPrint["result of 2nd step of em (substitutions): ", 
     tradi[TableForm[step3]]][3];
   step4 = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[oo[{li1__}, {li2__}], 
        oo[ein[{mu[1]}, And[li1]] \[And] ein[{mu[2]}, And[li2]]]]] &, 
     step3];
   ZPrint[
     "result of 3rd step of em (introduction of existential \
quantifier): ", tradi[TableForm[step4]]][3];
   step4];
emScanner[ausdruck_] :=
  Module[{outputs, le1, le2, aktausdruck, erg},
   erg = {};
   outputs = Cases[ausdruck, {oo[l1__], r___}, {0, Infinity}][[1]];
   le1 = Length[outputs];
   Do[aktausdruck = 
     Replace[ausdruck, outputs -> outputs[[iii]], {0, Infinity}];
    erg = Append[erg, aktausdruck], {iii, 1, le1}];
   erg = Replace[erg, oo[etwas_] -> etwas, {0, Infinity}];
   ZPrint["result of 4th step of em (multiplied expression): ", 
     tradi[TableForm[erg]]][3];
   erg];

em[ausdruck_ /;
    (Not[
       FreeQ[ausdruck, 
        alle[{lv1__}, 
         innen1_ /; 
          Not[FreeQ[innen1, 
            ein[{lv2__}, 
             innen2_ /; (Head[innen2] === And)]]]]]]) && (Head[
        ausdruck] =!= Or)] := 
  Module[{erg, ergAkt, wieviele, wo, was, wasAkt, wasNeu, wasNeuAkt, 
    endErg},
   erg = maxIndizierung[ausdruck];
   ZPrint["variables multiplied (preparing em): ", tradi[erg]][4];
   endErg = {};
   was = Cases[erg, ein[{mu__}, innen2_] /;
      ((Head[innen2] === And) && (Not[
          FreeQ[erg, 
           alle[{lv1__}, 
            innen1_ /; Not[FreeQ[innen1, ein[{mu}, innen2]]]]]])),
     {0, Infinity}];
   If[was === {}, Return[ausdruck]];
   wieviele = Length[was];
   ZPrint["number of existential quantifiers to be multiplied: ", 
     wieviele][4];
   If[wieviele == 1,
    wo = First[Position[erg, ein[{mu__}, innen2_] /;
        ((Head[innen2] === And) && (Not[
            FreeQ[erg, 
             alle[{lv1__}, 
              innen1_ /; Not[FreeQ[innen1, ein[{mu}, innen2]]]]]])),
       {0, Infinity}, 1]];
    was = First[was];
    wasNeu = emInnen[was];
    erg[[wo /. (List -> Sequence)]] = wasNeu;
    erg = emScanner[erg];
    ZPrint["M-expression 1 = ", was // tradi, 
      " transformed by function em: ", lve[erg] // tradi][4];
    endErg = erg,
    Do[ergAkt[ii] = erg;
     wasAkt = was[[ii]];
     wasNeuAkt = emInnen[wasAkt];
     ergAkt[ii] = 
      Replace[ergAkt[ii], wasAkt -> wasNeuAkt, {0, Infinity}];
     ergAkt[ii] = emScanner[ergAkt[ii]];
     ZPrint["M-expression ", ii, " = ", wasAkt // tradi, 
       " transformed by function em: ", lve[ergAkt[ii]] // tradi][4];
     endErg = Flatten[Append[endErg, ergAkt[ii]]], {ii, 1, wieviele}]];
   ZPrint["result of em: ", endErg][4];
   ZPrint["result of em with deleted cases: ", endErg][4];
   endErg = Map[standardization, endErg];
   endErg = DeleteDuplicates[endErg];
   ZPrint["duplicates deleted (tradi-output of em): ", 
     tradi[TableForm[endErg]]][3];
   endErg = Map[List, endErg];
   ZPrint[
     "em-output as list of lists in order to identify partial \
expressions: ", endErg][4];
   endErg];
em[ausdruck_Or] := (undefined; 
   ZPrint["Head of input of em must not be Or "][4]); 
em[ausdruck_ /; 
    FreeQ[ausdruck, 
     alle[{lv1__}, 
      innen1_ /; 
       Not[FreeQ[innen1, 
         ein[{lv2__}, innen2_ /; (Head[innen2] === And)]]]]]] :=
  (undefined; 
   ZPrint["To apply em some \[Exists] quantifier being the head of a \
conjunction must be in the scope of a \[ForAll] quantifier "][3]);

emExpressionQ[ausdruck_] := 
  Not[FreeQ[ausdruck, 
    alle[{lv_}, 
     innen_ /; 
      Not[FreeQ[innen, 
        ein[{lv2_}, innen2_ /; (Head[innen2] === And)]]]]]];
(*"emExpressionQ" prüft, ob die Anwendungsbedingungen für em \
vorliegen.*)

konjunktverdopplungS[disjunkte_ /; Head[disjunkte] =!= Or] :=
  Module[{se, que, ee, disneu },
   se = satExpression[disjunkte];
   se = se //. {False} :> False;
   se = se //. {sat} :> sat;
   If[((se === False) || (se === sat)) || (emExpressionQ[disjunkte] ===
        False),
    If[(se === False) || (se === sat), 
     ZPrint["expression ", tradi[disjunkte], " =" , se][2.5]; 
     disneu = se, 
     ZPrint["The expresssion, namely ", disjunkte, 
       " is not duplicated as em is not applicable, only qe will be \
applied\!\(\*
       StyleBox[\".\",\nFontSlant->\"Italic\"]\)"][2.5]; 
     disneu = qe[disjunkte]; 
     ZPrint["result of applying qe to expression: ", tradi[disneu]][
      2.5]],
    ZPrint["Duplication needed: ", 
      TableForm[tradi[disjunkte] \[And] tradi[disjunkte]], "\!\(\*
      StyleBox[\" \",\nFontSlant->\"Italic\"]\)qe will be applied to \
the first conjunct and em will be applied to the second conjunct."][
     2.5]; disneu = qe[disjunkte] \[And] em[disjunkte]; 
    ZPrint["result of applying qe and em to duplicated expression: ", 
      tradi[TableForm[disneu]]][2.5]];
   ZPrint["partial expression without Head=Or: ", tradi[disneu]][4]; 
   disneu];
konjunktverdopplungS[disjunkte_Or] :=
  Module[{lae, se, que, ee, disneu},
   lae = Length[disjunkte];
   ZPrint["number of disjuncts ", lae][4];
   Do[se = satExpression[disjunkte[[ii]]];
    se = se //. {False} :> False;
    se = se //. {sat} :> sat;
    If[((se === False) || (se === sat)) || (emExpressionQ[
         disjunkte[[ii]]] === False),
     If[(se === False) || (se === sat), 
      ZPrint["Disjunct no. ", ii, " nameley ", 
        tradi[disjunkte[[ii]]], " = ", se][2.5]; disneu[ii] = se,
      ZPrint["disjunct no. ", ii, " , namely ", 
        tradi[disjunkte[[ii]]], 
        " , is not duplicated as em is not applicable, only qe will \
be applied."][2.5]; disneu[ii] = qe[disjunkte[[ii]]]; 
      ZPrint["result of applying qe to disjunct no. ", ii, ":", 
        tradi[TableForm[disneu[ii]]]][2.5]],
      ZPrint["duplication of disjunct no. ", ii, " : ", 
       TableForm[
        tradi[disjunkte[[ii]]] \[And] tradi[disjunkte[[ii]]]], 
       " , qe will be applied to the first conjunct and em will be \
applied to the second conjunct."][2.5];
     disneu[ii] = qe[disjunkte[[ii]]] \[And] em[disjunkte[[ii]]]; 
     ZPrint["result of applying qe and em to duplicated disjunct no. \
", ii, " :", tradi[TableForm[disneu[ii]]]][2.5]], {ii, 1, lae}];
   disneu = Apply[Or, Table[disneu[ii], {ii, 1, lae}]];
   ZPrint["partial expression with Head=Or: ", tradi[disneu]][4]; 
   disneu];

terminierung[ausdruck_] := 
  Module[{kvargumente, klae, termstep3, termstep4, termstep5, 
    termstep8, erg}, erg = ausdruck;
   (*Im Folgenden bedienen wir uns eines Tricks und ersetzen alle \
innersten Teilausdrücke,die nicht sat oder False sind durch "nonsat". 
   Dieser Trick ist nötig,
   um Simplify und satDisjunktion auch auf komplexe Ausdrücke mit \
über 100 Teilausdrücken anwenden zu können.Dieser Tricke ist zulässig,
   da wir den Gesamtausdruck nur in Abhängigkeit zu "sat" und "False" \
Teilausdrücken asl sat oder False identifizieren wollen.Falls \
"ausdruck" nicht als False oder sat identifziert werden kann,
   wird mit "ausdruck" weiter gerechnet.*)
   kvargumente = 
    DeleteDuplicates[
     Cases[erg, {teilausdruck_} /; (teilausdruck =!= 
          sat) && (teilausdruck =!= False) && (teilausdruck =!= 
          True) && (Head[teilausdruck] =!= List) && 
        Not[xListeQ[{teilausdruck}]] && Not[yListeQ[{teilausdruck}]] &&
         FreeQ[teilausdruck, {uliste_} /; 
          Not[xListeQ[{uliste}]] && Not[yListeQ[{uliste}]]], {0, 
       Infinity}]];
   klae = Length[kvargumente];
   termstep3 = erg;
   If[klae > 0, 
    Do[termstep3 = 
      Replace[termstep3, 
       kvargumente[[ii]] -> {nonsat}, {0, Infinity}], {ii, 1, klae}]];
   (*ZPrint["termstep3 =",termstep3][3];*)
   termstep4 = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[{etw1__, 
          etw2__} /; (Not[xListeQ[{etw1, etw2}]] && 
           Not[yListeQ[{etw1, etw2}]]), {etw1 \[And] etw2}]] &, 
     termstep3];
   termstep4 = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[{etw_} /; (Not[xListeQ[{etw}]] && 
           Not[yListeQ[{etw}]]), (etw)]] &, termstep4];
   (*Der Zusatz \
"(Not[xListeQ[{etw1,etw2}]]&&Not[yListeQ[{etw1,etw2}]])" verhindert,
   dass die Kommata in Variablenlisten durch "\[And]" bzw.die \
geschweiften Klammern um die Variablen durch runde Klammern ersetzt \
werden.*)ZPrint["Expression to be evaluated as False or sat : ", 
     tradi[termstep4]][3];
   termstep5 = Simplify[termstep4];
   (*Es muss hier Simplify verwendet werden,
   da nur Simplify quantorenlogische Formel evaluiert.Simplify[
   ein[{y},f[y]\[And]\[Not]f[y]]]=False,
   gleiches gilt nicht für BooleanMinimize.*)
   If[termstep5 === False, 
    ZPrint["False evaluation by Simplify succeeded: ", 
      tradi[termstep5]][2]; Return[False], 
    ZPrint["False-evaluation by Simplify failed. "(*,tradi[
      termstep5]*)][3]];
   termstep8 = satDisjunktion[termstep5];
   If[termstep8 === sat, 
    ZPrint["sat evaluation by satDisjunction succeeded: ", 
      tradi[termstep8]][2]; Return[sat], 
    ZPrint["sat-evaluation by satDisjunction failed. "(*,tradi[
      termstep8]*)][3]];
   ZPrint["The following expression must be further evaluated: ", 
     erg][2]; erg]; 
(*"terminierung" prüft ob die logische Umformung des gesamten \
abgeleiteten Ausdruckes gemäß Simplify als False oder gemäß \
satDisjunktion als sat identifiziert werden dann. Ist dies der Fall, \
wird, "False" bzw. "sat" zurückgegeben. Dies bewirkt, dass in \
"decideiterativerTeil" keine weitere Iteration eingeleitet und das \
Programm terminiert. Ansonsten wird eine weitere Iteration \
eingeleitet, wobei
wieder auf den input von terminierung zurückgegangen wird.*) 

decideIterativerTeil[ausdruck__] := 
  Module[{kvargumente, klae, nachkv, kj, erg}, erg = ausdruck;
   While[(erg =!= sat) && (erg =!= False), 
    ZPrint["starting iteration"][1];
    kvargumente = 
     Cases[erg, {teilausdruck_} /; (Head[teilausdruck] =!= List) && 
        Not[xListeQ[{teilausdruck}]] && Not[yListeQ[{teilausdruck}]] &&
         FreeQ[teilausdruck, {uliste_} /; 
          Not[xListeQ[{uliste}]] && Not[yListeQ[{uliste}]]], {0, 
       Infinity}];
    ZPrint["partial expressions: ", tradi[kvargumente]][4];
    klae = Length[kvargumente];
    ZPrint["number of partial expressions: ", klae][4];
    If[klae > 0,
      Do[nachkv[ii] = 
       konjunktverdopplungS[emSimplifying[First[kvargumente[[ii]]]]]; 
      erg = 
       MapAll[ReplaceAll[#, 
          RuleDelayed[First[kvargumente[[ii]]], nachkv[ii]]] &, 
        erg], {ii, 1, klae}], erg = konjunktverdopplungS[erg]];
    ZPrint["Expression to evaluate by module terminierung ", 
      tradi[erg]][3];
    erg = terminierung[erg]];
   ZPrint["decide terminates with the result ", erg][1];
   erg];

eingabepruefung[ausdruck_] :=
  Module[{erg, vara, varwf},
   (* eingabepruefung prüft nicht,ob eine Variable gebunden ist!*)
   erg = ausdruck;
   vara = Length[Cases[ausdruck, {var_}, {0, Infinity}]];
   varwf = Length[Cases[wf[ausdruck], {var_}, {0, Infinity}]];
   If[varwf < vara, 
    Return["Input not well formed (superfluous quantifier?)"]];
   If[Not[FreeQ[ausdruck, Times]], 
    Return["Input not well formed (forgotten comma?)"]];
   If[Not[FreeQ[ausdruck, ein[etwas_]]], 
    Return[
     "Input not well formed (\[Exists] quantifier without variable or \
expression?)"]];
   If[Not[FreeQ[ausdruck, alle[etwas_]]], 
    Return["Input not well formed (\[ForAll] quantifier without \
variable or expression?)"]];
   If[Not[FreeQ[ausdruck, ein[ll_, etwas_] /; Head[ll] =!= List]], 
    Return["Input not well formed (quantifier variable not in \
list?)"]];
   If[Not[FreeQ[ausdruck, alle[ll_, etwas_] /; Head[ll] =!= List]], 
    Return["Input not well formed (quantifier variable not in \
list?)"]];
   If[Not[
     FreeQ[ausdruck, ein[{lk_}, etwas_] /; Not[FreeQ[etwas, {lk}]]]], 
    Return["Input not well formed (double defined quantifiers?)"]];
   If[Not[
     FreeQ[ausdruck, alle[{lk_}, etwas_] /; Not[FreeQ[etwas, {lk}]]]],
     Return["Input not well formed (double defined quantifiers?)"]];
   If[Not[FreeQ[ausdruck, oo]], 
    Return["Input not well formed (string oo not allowed)"]];
   ZPrint["input : ", tradi[erg]][1];
   erg];


(*EXPANSATION*)
(* Dieses Modul wird einmalig nach der eingabepruefung angewendet, um 
1. alle Junktoren bis auf And (&&,\[And])\[MediumSpace]\
\[FilledVerySmallSquare]\[MediumSpace] Or (||,\[Or])\[MediumSpace]\
\[FilledVerySmallSquare]\[MediumSpace] Not (!,¬) zu beseitigen,
  2. negative Normalformeln (NNF) zu generieren. 
Dies beides wird geleistet, indem LogicalExpand mittels "expansation" \
maximal angewendet wird. Ausserdem müssen Negationen vor Quantoren \
beseitigt werden, was Mathematica nicht im Rahmen von LogicalExpand \
macht.
Im weiteren Verauf des Algorithmus muss nicht mehr expandiert werden, \
da an keiner Stelle neue Junktoren eingeführt oder Negatoren nach \
aussen gebracht werden. *)

InnerhalbAlleexpand[expression_] :=
  Module[{erg},
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[alle[{nn__}, innen_], 
        alle[{nn}, Simplify[LogicalExpand[innen]]]]] &, expression];
   erg];
InnerhalbEinexpand[expression_] :=
  Module[{erg},
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[ein[{nn__}, innen_], 
        ein[{nn}, Simplify[LogicalExpand[innen]]]]] &, expression];
   erg];
negatedquantifierExpand[expression_] :=
  Module[{erg},
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[! ein[{xx_}, rest_], alle[{xx}, ! rest]]] &, 
     expression];
   erg = 
    MapAll[ReplaceAll[#, 
       RuleDelayed[! alle[{xx_}, rest_], ein[{xx}, ! rest]]] &, erg];
   erg];

expansionCore[expression_] :=
  Module[{erg},
   erg = expression;
   erg = LogicalExpand[erg];
   ZPrint["expression expanded: ", tradi[erg]][5];
   erg = InnerhalbAlleexpand[erg];
   ZPrint[
     "expression expanded within scope of universal quantifier: ", 
     tradi[erg]][5];
   erg = InnerhalbEinexpand[erg];
   ZPrint[
     "expression expanded within scope of existential quantifier: ", 
     tradi[erg]][5];
   erg = negatedquantifierExpand[erg];
   ZPrint["negations before quantifiers eliminated: ", tradi[erg]][5]; 
   erg = Simplify[erg];
   ZPrint["expression simplified according to Simplify: ", 
     tradi[erg]][5];
   erg];
expansion[expression_] :=
  Module[{erg},
   erg = Simplify[expression];
   ZPrint["expression simplified according to Simplify: ", 
     tradi[erg]][5];
   erg = FixedPoint[expansionCore, erg];
   ZPrint["input expanded: ", tradi[erg]][4];
   erg];

decide[ausdruck_] := 
  Module[{erg, di},
   erg = eingabepruefung[ausdruck];  
   If[StringQ[erg], Return[erg]];
   (* Diese Zeile ist nötig, damit nicht-
   wohlgeformte Ausdrücke nicht evaluiert werden.*)
   erg = lve[erg];
   erg=maxIndizierung[erg];
 (* erg = variableconverting[erg]; *)
   erg = expansion[erg];
   erg = standardization[erg];
   erg = terminierung[erg];
   di = decideIterativerTeil[erg];
   di];

(* PRINTBEFEHLE *)

ZPrint[toprint__][level_] := 
  If[level <= printproofstepslevel, Print[toprint]];
(* Es werden Printbefehle auf verschiedenen Ebenen definiert.
Der user kann das level umstellen, dann muss mit "Remove" + \
NeuEinlesen (=Shift+Enter in diesem Block) das neue level aktiviert \
werden.
Ausser diesem level sollte vom user nichts verändert werden.*)

(*printproofstepslevel = 5;*)
(*Diesen Befehl auskommentieren, wenn er im Rahmen der nb-Datei wirksam sein soll.*)

(*The following printproofstepslevels are available:
1. prints input, start of a new iteration and output of decide.
2. Adds to 1. the  non-iterative steps before the iteration and the \
results of iteration steps.
2.5. Adds to to 2. input and output of application of qe and em.
3. Adds to 2.5 the main steps of qe and em and further steps of the \
non-iterative part at the beginning of the whole algorithm and the \
steps concering the evalutation of each iteration result.
4. Adds to 3 more detailed steps of qe and em.
5. Adds to 4 details of subordinated functions.*)
  

(* Zur Zeit: Eingabe von logischen Ausdrücken in \
Mathematica-Schreibweise nötig (= InputForm). Folgende Junktoren sind \
erlaubt, aber nicht in der in Klammern zuletzt genannten \
traditionellen Schreibweise:
And (&&,\[And])\[MediumSpace]\[FilledVerySmallSquare]\[MediumSpace] \
Or (||,\[Or])\[MediumSpace]\[FilledVerySmallSquare]\[MediumSpace] Not \
(!,¬)\[MediumSpace]\[FilledVerySmallSquare]\[MediumSpace] Nand (\
\[Nand])\[MediumSpace]\[FilledVerySmallSquare]\[MediumSpace] Nor (\
\[Nor])\[MediumSpace]\[FilledVerySmallSquare]\[MediumSpace] Xor (\
\[Xor])\[MediumSpace]\[FilledVerySmallSquare]\[MediumSpace] Implies (\
\[Implies])\[MediumSpace]\[FilledVerySmallSquare]\[MediumSpace] \
Equivalent (\[Equivalent])\[MediumSpace]\[FilledVerySmallSquare]\
\[MediumSpace]
Für die Quantoren sind "alle[{v-Liste}, scope]" und "ein[{v-Liste}, \
scope]" zu verwenden. 
Da das Programm sehr schnell sehr komplizierte Ausdrücke erzeugt, \
empfiehlt es sich zunächst mit
"standardization[expansion[[inputformel]]" eine Disjunktion von \
Konjunktionen geschlossener Strukturen zu erzeugen und dann nur die \
einzelnen Disjunkte zu prüfen. Ist ein Disjunkt sat, ist inputformel \
sat. Sind alle Disjunkte False, ist inputformel False.*)

(* Grundstein für Interaktivmodul - es gibt aber Probleme bei der \
Eingabe, nur Mathematica-Ausdrücke sind erlaubt, esc nicht zu \
verwenden.*)
(*expressiontoevalutate=Input["Determine a logical expression of pure \
first-order logic?"];
eingabepruefung[expressiontoevaluate];
If[Not[eingabepruefung[expressiontoevaluate]==expressiontoevaluate],\
Break[],
printproofstepslevel=Input["Determine the level of explication?"];
decide[expressiontoevaluate]]*)


(*End[]*)

(*Protect[tradi,aqr2a,aqr3a,aqr2o,aqr3o,aqrpn1,aqrpn3,aqrpn5,aqrpn7,\
aqrpn9,aqrpn10,aqr,QuantorSimplify,JunctorSimplify,quantifizierenFA,\
quantifizierenEX,le,eq,TimmsElimination]*)

EndPackage[]
