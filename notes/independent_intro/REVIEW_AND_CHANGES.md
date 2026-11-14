# Nezávislé statementy: významová kontrola a přesný seznam změn

Datum: 2026-11-14. Výchozí formalizační main:
`1763dbbc5e8c9a72c9f92dbaa701e016b1eb8c1b`.
Pracovní větev: `verification/independent-intro-20261114`.

## Stav tří požadovaných kroků

1. Významová kontrola: **HOTOVO, všechny tři cíle odpovídají článku.**
2. Kompilace a mechanické opravy: **HOTOVO. Původní upload se zkompiloval
   bez chyby; jediná změna je zúžení importů.**
3. Propojení se stávajícími důkazy: **NEDOKONČENO.** Pracovní prostředí
   při zahájení implementace přestalo být dostupné. Žádná ze tří hlavních
   vět zatím není dokázána v nezávislém API.

Tento checkpoint neprohlašuje definice výroků za dokázané věty.
Původní dokončená formalizace zůstává na main beze změny.

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
importem. Předávací zpráva zůstává jako původní příloha u uživatele.

| Soubor | SHA-256 |
| --- | --- |
| Původní Lean upload | `c8c94e105065623be472cf0c1f4bc06225d87a324bf360bcebb483f0e32006b2` |
| Původní předávací zpráva | `4ce3989621a4add0b374071da1f856e787728eb58d4e19ef49ae1635cac5bea4` |
| Kompilovaná kopie | `cb03f5d89c63d400637efda49db18d56aa4e2e5a400edfd8a2492182f9b148fa` |

Kontrola `python3 tools/independent_intro/check_statements.py` ověřuje
neměnnost originálu, přesný povolený rozdíl importů a přesnost diffu.
Bude součástí CI. Po obnovení práce tak nelze nepozorovaně změnit
nezávislé cíle při doplňování důkazů.

## 3. Připravené propojení s důkazy a blokující výpadek

Jména cílových vět zůstávají `IndependentHypertournaments.intro_link`,
`IndependentHypertournaments.potential` a
`IndependentHypertournaments.intro_eppa`. Zatím nebyla přidána.

Připravený důkazový postup:

- Základní obousměrný převod mezi nezávislou úplnou ZMod-orientací a
  projektovým Bool-orientovaným `Hyper` na injektivních n-ticích, s důkazem
  obou roundtripů, přesné ekvivalence vnoření, řádů, evenness a potenciálu.
- Převod libovolné nezávislé rodiny zákazů na `ForbiddenFamily`; přesná
  ekvivalence `Forb`/ `Omits` a obou definic pair-cancelling.
- `intro_link`: `Ramsey.exists_ordered_ramsey_witness` a
  `Ramsey.pair_cancelling_ordering_property`, s přeznačením konečného
  witnessu na Fin a převodem monochromatičnosti na explicitní barvu.
- `potential`: `Hyper.exists_potential_fin`, `IsPotential.isEven`,
  `Ramsey.exists_potential_ramsey_witness` a
  `Ramsey.potential_expansion_property`. Přenést libovolné potenciály a
  řády zpět na nativní nosič až po výběru společného witnessu.
- `intro_eppa`: převod parciálních automorfismů mezi totálními mapami
  a bijekcemi podmnožin, převod tříd a jejich SAP/heredity/neomezenosti,
  potom `unbounded_hereditary_SAP_not_EPPA`,
  `pair_cancelling_not_EPPA` a `even_five_not_hasEPPA`.

Výpadek nastal během prvních zápisů převodních modulů. Jejich úspěšný zápis
a kompilace nebyly potvrzeny, proto nejsou zařazeny mezi ověřené produkční
soubory tohoto checkpointu. Shell následně hlásil
`No usable execution environment is available`; dostupný stav prostředí
je výslovně `unavailable`. Části 1 a 2 byly dokončeny před výpadkem.

Před označením části 3 za hotovou je nutné dopsat a zkompilovat převody,
dokázat přesné tři cíle, získat nezávislou recenzi převodů a provést úplný
build a axiomový audit včetně namespace `IndependentHypertournaments`.
Větev zůstává oddělená od main.
