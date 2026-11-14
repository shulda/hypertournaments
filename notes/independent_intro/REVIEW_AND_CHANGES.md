# Nezávislé statementy: významová kontrola a přesný seznam změn

Datum: 2026-11-14. Výchozí formalizační main:
`1763dbbc5e8c9a72c9f92dbaa701e016b1eb8c1b`.
Pracovní větev: `verification/independent-intro-20261114`.

## Stav tří požadovaných kroků

1. Významová kontrola: **HOTOVO, všechny tři cíle odpovídají článku.**
2. Kompilace a mechanické opravy: **HOTOVO. Původní upload se zkompiloval
   bez chyby; jediná změna je zúžení importů.**
3. Propojení se stávajícími důkazy: **HOTOVO.** Všechny tři přesné cíle
   mají důkazy v nezávislém API a prošly místním Leanem i nezávislou recenzí
   převodů. Celý projekt prošel buildem a úplným axiomovým auditem.

Definice výroků zůstávají v samostatném modulu; jejich důkazy jsou oddělené.
Původní dokončená formalizace zůstává na main beze změny, tato práce je
v samostatné ověřovací větvi.

## 1. Významová kontrola

**Žádná významová oprava není potřebná.** Tři části prošly oddělenými
nezávislými recenzemi, kromě kontroly integrátorem.

Kontrolovaným článkem je `on_homogeneous_hypertournaments.tex` v
`shulda/tex_hypertournaments`, commit
`a732651c134c099ed9de16f49f6aeb0368696678`, SHA-256 kontrolované lokální kopie
`ef7f27b401ec672ee46512ead36a3deef445450655fa1a28712164ee1ff18b17`.
Předávací zpráva jmenuje zdroj `on_homogeneous_hypertournaments (3).tex`,
ale neobsahuje jeho hash; totožnost celé této starší kopie ze zprávy
ověřit nelze. Proto jsme definice i cíle porovnali přímo s aktuálním článkem.
Oproti staršímu formalizačnímu pinu
`919349e7eceed3c7fa0ed126a337c6fae6624704` se relevantní hlavní věty ani
jejich matematické definice nezměnily.

Čísla Lean řádků odkazují na nezměněný upload, řádky článku na aktuální pin.

| Nezávislá definice / cíl | Lean řádky | Zdroj v článku | Výsledek kontroly |
| --- | --- | --- | --- |
| Hypertournament, Embeds | 24–29, 52–57 | Preliminaries, 175–221 | Střídavost pro transpozice je ekvivalentní úplnému permutačnímu zákonu. Nulové rozšíření na degenerované n-tice je jednoznačné pomocné kódování; při injektivním vnoření nepřidává omezení. |
| Volné striktní řády | 32–41, 60–64 | Preliminaries, 215–217 | Irreflexivita, tranzitivita a srovnatelnost různých prvků dávají striktní lineární řád. Žádná vazba na orientaci se nevyžaduje. |
| PairCancelling | 70–91 | def:pair-cancelling, 411–428 | Správné meze arity a velikosti. První dvě pozice tvoří daná dvojice a roste přesně zbytek n-tice. Řády na celé množině jsou ekvivalentní řádům na doplňku dvojice. |
| Forb | 96–98 | Preliminaries, 219–221 | Zakazuje skutečné indukované kopie. Rodina může být nekonečná i prázdná; nemusí se předem požadovat uzavřenost na izomorfismy. |
| RamseyOrdered, OrderingProperty | 104–130 | Ramsey classes, 316–349 | Ramseyův witness je před obarvením, ordering witness před oběma řády. Obarvení všech zobrazení je ekvivalentní obarvení vnoření, protože závěr testuje jen vnoření a r ≥ 2 dává výchozí barvu. |
| IntroLinkStatement | 135–139 | thm:intro-link, 86–92 | Všechny arity od tří, libovolná rodina PC zákazů, oba závěry. |
| coboundary, IsEven | 146–155 | Potential constructions, 704–726 | Fin.succAbove vynechá zvolenou souřadnici a zachová pořadí ostatních. Součet i evenness jsou přesně z článku. |
| PotentialExpansion, PotentialEmbeds | 163–180 | Definice potenciálu a expanze | Potenciál je skutečná střídavá orientace nižší arity, při vnoření pojmenovaná a zachovávaná. Rovnost s coboundary se správně požaduje jen na injektivních n-ticích. |
| PotentialRamsey, PotentialExpansionProperty | 183–210 | thm:potential a definice expansion property | Jeden even redukt B je zvolen před oběma potenciály i oběma řády. Expanze mají přesně dané redukty. |
| PotentialExpandsEven | 217–220 | Definice expanze; lem:alternating-sums; identity coboundary | Explicitně požaduje přesnost reduktové třídy včetně existence potenciálu. Jde o závěr, nikoli dodaný předpoklad. Zabraňuje vakuozitě. |
| IntroPotentialStatement | 226–229 | thm:potential, 104–107 | k ≥ 2 sudé přesně odpovídá lichému n = k+1 ≥ 3. |
| Parciální automorfismy a HasEPPA | 240–267 | EPPA, 969–975 | Parciální bijekci lze doplnit identitou mimo doménu. Jeden konečný witness a jedno vnoření fungují pro všechny parciální automorfismy. Plný automorfismus je bijektivní. |
| Heredita, neomezenost, SAP | 270–292 | Amalgamation, 293–314 | Uzavřenost zahrnuje přeznačení; SAP dovoluje libovolná vnoření a přesný průnik. JEP plyne z heredity, neomezenosti a SAP přes prázdný objekt. |
| IntroEPPAStatement | 295–314 | thm:intro-eppa, 114–122 | Všechny tři položky, správné meze n ≥ 6, n ≥ 4 a even arita právě pět. |

Zkontrolovány byly i prázdné a malé nosiče. Žádný cíl nezávisí na volbě
kanonického potenciálu, dodatečném řádu neuspořádaného reduktu, konečnosti
rodiny zákazů nebo silnějším pojmu vnoření.

Rozsah této nezávislé kontroly je přesně trojice hlavních vět z úvodu.
Soubor nevyslovuje všechny pomocné věty, klasifikace a pozdější zobecnění
článku. Dříve vynechaný důsledek o kontinuu struktur sem nepatří.

## 2. Kompilace a mechanické změny

Původní upload byl zkompilován **beze změny** pomocí Leanu 4.34.1 a Mathlib
na projektovém pinu `d13f23b723b8a846827a245b89c10fc7d3f11612`:

```sh
lake env lean /workspace/scratch/29552594b314/upload/independent_hypertournament_statements.lean
```

Výsledek byl **exit 0, žádné chyby ani varování**. Žádné syntaktické,
elaborační nebo typové opravy nebyly potřebné. Úspěšná kompilace samotných
definic výroků není důkazem jejich pravdivosti.

Jediná změna v kompilované kopii:

```diff
-import Mathlib
+import Mathlib.Data.ZMod.Basic
+import Mathlib.Algebra.BigOperators.Group.Finset.Defs
```

Důvodem je projektový zákaz širokých importů Mathlib a explicitní uvedení
použité konečné sumace. Změna se netýká žádné definice, typu, kvantifikátoru,
pole struktury, jména ani komentáře. Kompilovaná kopie
`Hypertournaments/Independent/Statements.lean` rovněž prošla s exit 0 před
výpadkem prostředí.

Přesný unified diff je [statements.patch](statements.patch). Původní Lean
upload je uchován beze změny v [original/independent_hypertournament_statements.lean.txt](original/independent_hypertournament_statements.lean.txt).
Přípona .txt zabraňuje jeho záměně za další produkční Lean modul se širokým
importem. Původní předávací zpráva je rovněž uchována beze změny jako
[original/independent_hypertournament_handoff.md.txt](original/independent_hypertournament_handoff.md.txt).

| Soubor | SHA-256 |
| --- | --- |
| Původní Lean upload | `c8c94e105065623be472cf0c1f4bc06225d87a324bf360bcebb483f0e32006b2` |
| Původní předávací zpráva | `4ce3989621a4add0b374071da1f856e787728eb58d4e19ef49ae1635cac5bea4` |
| Kompilovaná kopie | `cb03f5d89c63d400637efda49db18d56aa4e2e5a400edfd8a2492182f9b148fa` |

Kontrola `python3 tools/independent_intro/check_statements.py` ověřuje
neměnnost obou originálů, přesný povolený rozdíl importů a přesnost diffu.
Je součástí CI. Při doplňování důkazů tak nelze nepozorovaně změnit
nezávislé cíle při doplňování důkazů.

## 3. Dokázané věty a zachování nezávislosti

Produkční vstupní modul je `Hypertournaments/Independent/Theorems.lean`:

```lean
IndependentHypertournaments.intro_link : IntroLinkStatement
IndependentHypertournaments.potential : IntroPotentialStatement
IndependentHypertournaments.intro_eppa : IntroEPPAStatement
```

Současně exportuje `all_intro_statements`, konjunkci těchto tří přesných
výroků bez dalších předpokladů. Není zde žádný nedokázaný provider nebo
podmíněná redukce nahrazující původní větu.

| Přidaný modul | Úloha a důvod |
| --- | --- |
| `Statements.lean` | Samostatné nezávislé definice a cíle. Neimportuje žádnou definici ani větu formalizačního projektu. Přesný rozdíl vůči uploadu jsou pouze dva specifické importy. |
| `BasicBridge.lean` | Oba převody orientací na stejném nosiči, obě skutečné strukturální inverze, ekvivalence vnoření, evenness, potenciálové rovnice a volných striktních řádů. |
| `ClassBridge.lean` | Přesné ekvivalence `Forb`/`Omits`, obou linkových definic a pair-cancelling včetně velikostí, pořadí dvojice a libovolných řádů. |
| `LinkBridge.lean` | Důkaz `intro_link`, obousměrný převod uspořádaných vnoření a explicitní přeznačení konečných witnessů. |
| `PotentialBridge.lean` | Důkaz `potential`: přesná reduktová třída, Ramsey i expansion property pro libovolné potenciály a řády. |
| `EPPABridge.lean` | Převod parciálních automorfismů a EPPA, libovolných tříd a jejich heredity/SAP/neomezenosti; důkazy všech tří EPPA položek. |
| `Theorems.lean` | Společný vstupní modul a konjunkce tří nezávislých cílů. |

### Reprezentace, libovolné rodiny a třídy

`toHyper` a `ofHyper` zachovávají nosič. Jsou dokázány obě rovnosti
`toHyper (ofHyper A) = A` a `ofHyper (toHyper A) = A`, nikoli jen podobnost
výstupů nebo existence abstraktního izomorfismu. To je podstatné pro libovolné
predikáty F a K, které samy nemusí být předem uzavřené na izomorfismy.
Zvlášť se dokazuje, že rovnost orientací všech totálních n-tic je ekvivalentní
projektovému `Preserves` na injektivních n-ticích; degenerované n-tice se
zpracují pomocí předepsané nulové hodnoty.

### Použité existující výsledky

| Nezávislý cíl | Existující dokázané výsledky |
| --- | --- |
| `intro_link` | `Ramsey.exists_ordered_ramsey_witness`, `Ramsey.pair_cancelling_ordering_property` |
| `potential`, přesná reduktová třída | `Hyper.exists_potential_fin`, `IsPotential.isEven` |
| `potential`, Ramsey | `Ramsey.exists_potential_ramsey_witness` |
| `potential`, expansion property | `Ramsey.potential_expansion_property`, `IsPotential.of_equiv_pullback` |
| `intro_eppa`, (i) | `unbounded_hereditary_SAP_not_EPPA` |
| `intro_eppa`, (ii) | `pair_cancelling_not_EPPA` |
| `intro_eppa`, (iii) | `even_five_not_hasEPPA`, skutečná ekvivalence switching admissibility a evenness |

Převody jsou součástí důkazů: žádná ekvivalence mezi nezávislou a projektovou
definicí není předpoklad. Samotné původní matematické moduly se nemění.

### Citlivé kvantifikátory a hraniční případy

- Ramseyův witness se volí před obarvením. Převod nativní párové
  monochromatičnosti na explicitní společnou barvu zvlášť řeší prázdnou
  množinu vnoření zdroje do prostředního objektu.
- Ordering witness se volí před oběma řády. Přeznačení přes `Fin` nemění
  redukt witnessu při následné volbě libovolného cílového řádu.
- Expanční witness se volí před oběma potenciály i řády. Po aplikaci nativní
  věty je dokázaná rovnost návratové expanze s přesně danou cílovou expanzí:
  redukt, pojmenovaný potenciál i striktní řád.
- EPPA převod zpracuje každý nativní izomorfismus podmnožin pomocí totálního
  zobrazení s identitou mimo doménu. Jeden witness a jedno vnoření se volí
  před všemi parciálními automorfismy. Výsledná prodloužení jsou bijektivní
  automorfismy. Prázdné nosiče a degenerované n-tice jsou zahrnuté.
- SAP se přenáší pro libovolná dvě vnoření a se stejnou podmínkou přesného
  průniku. U even arity pět se členství cílového witnessu přenáší zpět do
  celé původní třídy, ne jen do vybrané podtřídy.

## 4. Další integrační změny

Vedle import-only diffu samotných statementů vznikly převodní moduly,
recenze a ověřovací záznam. Projektový facade nyní importuje společný modul
`Independent.Theorems`; čitelné axiomové kontroly zahrnují nové cíle a
klíčové převody. README uvádí nezávislé rozhraní a AGENTS zachovává pravidlo
neměnnosti statementů a oddělené pracovní větve.

Ve třech nových převodních souborech byla po recenzi odstraněna jediná
nadbytečná prázdná koncová řádka. Dodatek nezávislé recenze ověřuje přesnou
rovnost původních a výsledných bajtů až na tento jeden LF a uvádí konečné
hashe. Následný úplný build a audity proběhly na těchto konečných verzích.

CI navíc spouští kontrolu původních hashů a přesného diffu. Axiomový nástroj
vybírá deklarace podle **definičních modulů**, nikoli podle jejich jmenných
prostorů. Původní checkpoint měl pro dodatečnou kontrolu nesprávný kořen
`IndependentHypertournaments`; dokončená větev jej opravuje na
`Hypertournaments.Independent`. Celkový kořen `Hypertournaments` nové moduly
již zahrnuje, včetně soukromých pomocných deklarací. Doplňkových 191 deklarací
se proto do celkového počtu nezapočítává podruhé.

## 5. Ověření

Po obnovení místního prostředí byly všechny důkazy vyvíjeny a kontrolovány
místním Leanem. Actions slouží jen k závěrečné kontrole publikovaného commitu.

- Lean 4.34.1; beze změny pinu Mathlib a neměnného převzatého Ramsey kódu.
- Úplný `lake --rehash build`: **2230 úloh, úspěch**.
- Source guard: **519 projektových modulů**, 518 v importním facade a
  samostatný `AxiomAudit`; všech 119 převzatých modulů; 96 specifických
  externích kořenů Mathlib. Žádné placeholdery nebo vlastní axiomy.
- Samostatné kompilace nových převodních modulů prošly bez diagnostiky.
- Všech deset regresních testů source guardu i oba generátory konečné
  klasifikace s `--check` prošly.
- Čitelné axiomové kontroly přesných tří vět i jejich společné konjunkce
  prošly.
- Úplný audit: **5436 Hypertournaments + 117 CCO + 1700 PartiteConstruction
  + 805 SuccessorTree = 8058 deklarací**, pouze `propext`, `Classical.choice`
  a `Quot.sound`, bez porušení allowlistu.
- Doplňkový audit nových modulů `Hypertournaments.Independent`: **191**
  deklarací, zahrnutých již v celkovém auditu výše.

Nezávislé recenze s přesnými zdrojovými hashi jsou `BRIDGE_REVIEW.md` a
`EPPA_BRIDGE_REVIEW.md`. Hashové vazby a výsledky kontrol jsou ve
`verification.json`. Přesný publikovaný commit a výsledek jeho CI patří do
PR #418, aby nevznikala kruhová závislost mezi hashem commitu a jeho obsahem.
Větev zůstává oddělená od main podle zadání uživatele.
