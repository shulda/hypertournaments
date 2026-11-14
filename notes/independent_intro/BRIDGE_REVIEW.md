# Nezávislá matematická recenze převodních důkazů

Datum: 2026-11-14. Recenzent: samostatný agent
`/root/independent_bridge_review`, který nepsal recenzované důkazy.

## Výsledek a rozsah

**PASS. V pěti převodních modulech ani v závěrečném konjunkčním modulu nebyla nalezena významová mezera,
zesílený předpoklad ani oslabený závěr.** Důkazy skutečně vedou k přesným
nezávislým cílům `intro_link`, `potential` a `intro_eppa`; nevydávají
pouhou kompilaci definic výroků za důkaz.

Recenze vycházela z přesných zdrojů načtených přes neměnné Git blob SHA.
SHA-256 jejich dekódovaného UTF-8 obsahu byl nezávisle přepočten a souhlasí
s lokálně kompilovanými verzemi implementátorů. Recenzent nezměnil žádný
produkční Lean soubor. Vlastní matematická kontrola převodů je oddělena
od kompilace, úplného buildu, axiomového auditu a kontroly CI, které provádí
integrátor.

Nezávislé znění pokrývá tři hlavní věty z úvodu článku, nikoli všechny
pomocné věty, klasifikace a závěrečné zobecnění. Pro významovou shodu
samotných cílových definic platí také oddělené recenze zaznamenané
v `REVIEW_AND_CHANGES.md`.

## Zmrazené zdroje

Všechny níže uvedené Lean soubory jsou v
`Hypertournaments/Independent/`.

| Soubor | SHA-256 |
| --- | --- |
| Statements.lean | `cb03f5d89c63d400637efda49db18d56aa4e2e5a400edfd8a2492182f9b148fa` |
| BasicBridge.lean | `44a9ff88442bdfe4f4d97ecf022793306fda8b0758ce0496b24a9c55c957aca8` |
| ClassBridge.lean | `956df22323364fdf61d32e61bc8e297d48e9a0c60698c2f26ac64d6265cb6fa7` |
| LinkBridge.lean | `155b326ad6b90844f3bed1d0707c5804cb58528bcc426f02083817f38afcac56` |
| PotentialBridge.lean | `b015b39ef75e67da9d6d058a4eae88c061c7808177c457f74288a25d48e2c35d` |
| EPPABridge.lean | `1c9916c615fd6963fd295c4cfbe2c448c0806c64ba903090bca41b4cec70bf18` |
| Theorems.lean | `d0a8ee1337b82c54bf6f29ae729fe2e46f887433ff90f7a70f037d1ac22cfe34` |

Přesné recenzované Git bloby:

- BasicBridge: `caa35028cce9c2c1a0869d6550f61d05de5c75b2`.
- ClassBridge: `20bbc497aff86f687e08acdfb6784b90e5c14d09`.
- LinkBridge: `21128176b94937753c199f4ed8802e03a3a84468`.
- PotentialBridge: `bb3eb727fbfe0b375679179307b80c70e578ff7b`.
- EPPABridge: `555b02c5651b70b70e31981157a3764c98b58e28`.

## 1. Přesnost základního kódování

`BasicBridge` převádí úplnou nezávislou ZMod-orientaci na projektovou
Bool-orientaci injektivních n-tic na **téže množině vrcholů**. Hodnoty
orientace se zachovávají přes dokázané převody `p1BitToZMod` a
`p3ZMod2ToBool`, nikoli pouze až na globální obrácení orientace.

Jsou dokázány obě skutečné strukturální rovnosti
`toHyper (ofHyper A) = A` a `ofHyper (toHyper A) = A`. Druhá kontroluje
také degenerované n-tice přes jejich standardní nulovou hodnotu.
To je zásadní pro libovolné predikáty F a K: nikde není potichu předpokládána
jejich uzavřenost na izomorfismy.

`embeds_iff_preserves` má oba směry a pokrývá všechny úplné n-tice
nezávislé definice. Degenerované n-tice zůstávají degenerované po složení
s injekcí, takže jejich nulové hodnoty nepřidávají omezení.

`tupleCoboundary_toHyper`, `isEven_iff` a `isPotential_iff` používají
přesně součet všech uspořádaně vynechaných stěn. Kompatibilita potenciálu
zůstává omezena na injektivní n-tice, jak vyžaduje článek.
Nevkládá se nepodložená rovnost na degenerovaných n-ticích.

Převody řádů zachovávají doslova původní striktní relaci. Oba příslušné
lt-lemma jsou bodové ekvivalence. Nevzniká žádná podmínka slučitelnosti
řádu s orientací.

## 2. Libovolné rodiny zákazů a pair-cancelling

`nativeFamily F m A := F ⟨m, ofHyper A⟩` zachycuje každou nezávislou
zakázanou strukturu díky oběma skutečným roundtripům. Dokázané
`omits_iff` je ekvivalence mezi úplným `Forb` a `Omits`, nikoli pouze
jednosměrná implikace pro vybranou podrodinu.

Dva linkové převody zachovávají stejné první dvě souřadnice, stejné
striktně rostoucí zbývající souřadnice a původní řád. Pomocná mez n ≥ 2
je odvozena z n ≥ 3 ve skutečné PC definici; nezesiluje cílovou větu.
`pairCancelling_iff` zachovává meze arity a velikosti i kvantifikaci všech
dvojic a všech řádů. Nerovnost ZMod-hodnot je ekvivalentní nerovnosti
Bool-hodnot díky injektivitě dokázaného hodnotového převodu.

Rodina F může být nekonečná i prázdná a nemusí být sama izomorfně uzavřená.

## 3. Linkový Ramseyův a ordering důkaz

V Ramseyově části je nativní witness vybrán před obarvením.
Jeho libovolný konečný nosič X je přeznačen skutečnou ekvivalencí s
`Fin (Fintype.card X)`. Na nativní vnoření se aplikuje přesně původní
barva odpovídajícího zobrazení po tomto přeznačení.

Převod párové monochromatičnosti na explicitní existenci barvy správně
rozlišuje neprázdný a prázdný prostor vnoření A do B. V prvním případě
se vybere jedno vnoření jako základní barva. Ve druhém je barva nula
přípustná a každé předpokládané nezávislé vnoření by dalo nativní vnoření,
čímž by vznikl spor. Nezavádí se předpoklad, že A již musí být vnořitelné
do B.

V ordering části je redukt B a jeho přeznačení zvolen před oběma libovolnými
řády oa a ob. Teprve po ob se tento řád transportuje zpět na nativní nosič;
**redukt se přitom nemění**. Výsledné vnoření tak skutečně směřuje do
téhož předem zvoleného B s přesně požadovaným ob.

Pomocné nativní převody zachovávají i reflektují obě relace úplného
uspořádaného jazyka, ne pouze kladné orientované n-tice.

## 4. Potenciálový důkaz a nevakuozita

`potentialExpandsEven_of_even` dokazuje jak existenci potenciálové
expanze každého even objektu, tak evenness každého reduktu expanze.
Existence zahrnuje prázdný nosič a nevybírá žádnou kanonickou třídu
potenciálů pro pozdější univerzální cíle.

Ramseyův důkaz uchovává horní orientaci, pojmenovaný dolní potenciál i
řád. Přeznačení nemění ani jeden z těchto údajů až na prokázaný transport.
Převod barev opět řeší prázdný prostor zdrojových vnoření.

U expansion property kód nejprve zvolí W, B a ekvivalenci s, a **až poté**
kvantifikuje přes libovolné Astar, Bstar a rovnosti jejich reduktů.
Potenciál a řád libovolného Bstar se přenesou zpět po s.symm na nativní W.
Původní nativní theorem se použije na tento libovolný potenciál a řád.

Závěrečné `hreturn` prokazuje rovnost transportované expanze s přesně
zadaným Bstar ve všech třech datech: reduktu, pojmenovaném potenciálu
a striktním řádu. Cílový potenciál se nenahrazuje jiným reprezentantem.
Konečné vnoření zachovává obě orientace i řád.

Vnější indexování sudým k odpovídá přesně lichému n = k+1 ≥ 3 a všechny
předpoklady nativních výsledků jsou odvozeny z původního cíle.

## 5. EPPA, částečné automorfismy a obecné třídy

`partialTotal` reprezentuje každou nativní bijekci mezi podmnožinami
totální mapou, která mimo doménu je identita. Nepotřebuje výběr výchozího
vrcholu, takže funguje i na prázdném nosiči.

Důkaz `partialTotal_isPartialAutomorphism` kontroluje obraz domény,
injektivitu na doméně, surjektivitu na cílovou podmnožinu a zachování
všech relevantních orientací. U injektivních n-tic používá skutečný
nativní podmnožinový izomorfismus. U degenerovaných n-tic se správně
odvodí degenerovanost složení a použijí nulové hodnoty.

`hasEPPA_to_nativeClass` nejprve zvolí jeden B a jedno vnoření a až potom
uvažuje libovolný nativní parciální automorfismus. Prodloužení g je plná
bijekce, převedená přes `Equiv.ofBijective` na skutečný nativní
automorfismus. Obyčejné EPPA nevyžaduje koherentní společnou volbu těchto
prodloužení a kód ji ani nepředpokládá.

Heredita, neomezenost a SAP se přenášejí pro libovolný predikát K přes
přesné roundtripy. Přenášejí se všechny diagramy, stejné mapy,
komutativita a přesný průnik; SAP není nahrazeno tvrzením pouze pro inkluze.

Tři závěrečné části používají přesně odpovídající starší negativní věty.
Ve druhé části se explicitně převádí členství tříd Forb/Omits na vstupu
i výstupním witnessu. Ve třetí části se totéž dokazuje mezi skutečnou
evenness v aritě pět a lokální switching omission třídou. Nezůstává
nevyřízená podmínka, že vybraný witness musí patřit do požadované třídy.

## 6. Závěrečný společný cíl

Přesný zdroj `Theorems.lean` dodaný integrátorem byl rovněž nezávisle
zkontrolován a jeho SHA-256 přepočten. Vyslovuje bez dalších předpokladů
`IntroLinkStatement ∧ IntroPotentialStatement ∧ IntroEPPAStatement`
a dokazuje jej trojicí `⟨intro_link, potential, intro_eppa⟩`. Neobsahuje
náhradu cílových definic ani dodatečné podmínky.

Recenze tak pokrývá všech sedm nových Lean modulů: nezávislé definice,
pět převodních důkazů a závěrečný společný cíl.

## Integrační podmínky a rozsah auditu

Matematická recenze má výsledek PASS pro zmrazené zdroje výše.
Integrátor musí připojit úplný build, úplný axiomový audit a zelené CI
přesného publikovaného commitu. Readable audit má kontrolovat skutečné
dokázané věty, nikoli pouze definice jejich výroků.

Nástroj axiom-audit vybírá kořeny **definujících modulů**, nikoli namespace
jmen deklarací. Nové deklarace mají namespace IndependentHypertournaments,
ale jejich definující moduly leží pod Hypertournaments.Independent.
Kompletní audit kořene Hypertournaments je proto zahrnuje včetně privátních
pomocných deklarací. Samostatný audit Hypertournaments.Independent je
užitečná kontrola tohoto podstromu, ale je podmnožinou úplného projektového
auditu a jeho počet se nesmí do celkového součtu přičíst podruhé.
Vnější namespace IndependentHypertournaments sám není správný modulový
kořen auditu.

Změna některého recenzovaného zdroje vyžaduje kontrolu nového hashe
a příslušného rozdílu.

## Dodatek: normalizace konce souborů po recenzi

Integrátor při závěrečné kontrole diffu odstranil z BasicBridge.lean,
ClassBridge.lean a LinkBridge.lean právě jeden nadbytečný koncový LF.
Recenzent tuto normalizaci nezávisle ověřil přímo z výše uvedených
recenzovaných neměnných blobů: pro každý soubor platí
`původní_obsah = normalizovaný_obsah + "\n"` a změna je přesně
`.replace(/\n\n$/, "\n")`. Nezměnil se žádný logický token,
řádek důkazu, předpoklad ani cíl.

Aktuální konečné vazby těchto tří souborů jsou:

| Soubor | Konečný SHA-256 po normalizaci |
| --- | --- |
| BasicBridge.lean | `f854cee43c90647a4eae090ba2bf75050b8a7142e314f48efa08685836661deb` |
| ClassBridge.lean | `07df929cd8d9ae001e69db4d19032b8232f9b71c72b7ddf2b4e77c5b4808c831` |
| LinkBridge.lean | `5378e89545665af62495e1ce96258310a264ea45b3d9a2a8baa97d075a6cd9be` |

Původní řádky hlavní tabulky a Git blob identifikátory zůstávají jako
historie přesně přečtených zdrojů. Pro konečnou integraci platí místo nich
tři nové hashe v tomto dodatku; ostatní čtyři zdrojové hashe jsou beze
změny. Matematický výsledek recenze zůstává **PASS**.
Úplný build a axiomové audity konečných normalizovaných souborů dokládá
integrátor.
