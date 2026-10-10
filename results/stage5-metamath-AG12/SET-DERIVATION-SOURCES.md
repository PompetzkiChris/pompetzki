# Named set derivations verified in the source

Source: `C:/ClaudeOutput/formalization-toolchain-20260924/libraries/metamath-set-mm-28167ed89a49/set.mm`. Each row was extracted from its actual `$p` assertion declaration. Lines are one-based source line numbers. These are source assertions and dependency references, not JDG1 acceptance results.

## axinf

Source declaration starts at line 102756.

```text
|- E. y ( x e. y /\ A. z ( z e. y -> E. w ( z e. w /\ w e. y ) ) )
```

Compressed-proof reference table:

```text
com cvv wcel wel wa wex wi wal omex inf0 ax-mp
```

## axinf2

Source declaration starts at line 102684.

```text
|- E. x ( E. y ( y e. x /\ A. z -. z e. y ) /\ A. y ( y e. x -> E. z ( z e. x /\ A. w ( w e. z <-> ( w e. y \/ w = y ) ) ) ) )
```

Compressed-proof reference table:

```text
c0 cv wcel wel csuc wi wal wa wex wn wceq com eleq2 wrex df-rex bitri wo wb peano1 peano2 ax-gen zfinf inf2 inf3 imbi12d albidv spcev mp2an 0el anbi12d sucel imbi2i albii anbi12i exbii mpbi
```

## inf0

Source declaration starts at line 102338.

```text
|- ( _om e. V -> E. y ( x e. y /\ A. z ( z e. y -> E. w ( z e. w /\ w e. y ) ) ) )
```

Compressed-proof reference table:

```text
vv vf com wcel cv cvv csuc wel wa wex wi c0 cfv wceq eleq2 cmpt crn wal crdg cres fr0g elv wfn frfnom peano1 fnfvelrn mp2an eqeltrri wrex fvelrnb ax-mp fvex sucid sucex eqid suceq frsucmpt2 mpan2 eleqtrrid eleq1 peano2b wb imbitrid mpan sylbi jca2 anbi12d syl6com rexlimiv ax-gen cdm wfun fndm spcev id eqeltrid fnfun funrnex mpisyl anbi2d exbidv albidv spcegv mp2ani imbi12d syl
```

## omex

Source declaration starts at line 102745.

```text
|- _om e. _V
```

Compressed-proof reference table:

```text
vx vy com cv wss cvv wcel vex ssex c0 csuc wral zfinf2 wel ax-1 ralimi2 wa wi peano5 sylan2 eximii exlimiiv
```

## dfac5

Source declaration starts at line 111913.

```text
|- ( CHOICE <-> A. x ( ( A. z e. x z =/= (/) /\ A. z e. x A. w e. x ( z =/= w -> ( z i^i w ) = (/) ) ) -> E. y A. z e. x E! v v e. ( z i^i y ) ) )
```

Compressed-proof reference table:

```text
vf vt vh cv c0 wne wral cin wceq wi wa wcel wex wal weq wac weu wfn cfv vu dfac4 crn neeq1 cbvralvw anbi2i r19.26 bitr4i pm3.35 ancoms ralimi wel sylbi wb elin fvelrnb biimpac fveq2 id eleq12d neeq2 ineq2 eqeq1d imbi12d wrex anbi12d rspcv wn minel imim2d imp necon4ad eleq1 biimpar impel eqeq2 eqcom bitrdi imbitrid ad2antrl mpd exp32 syl6com com14 rexlimdv syl5 expd ex com4t imp4b biimtrid sylan2br anassrs adantlr expcom anim12d imbitrrdi fnfvelrn com13 imp31 syl5ibrcom adantr impbid alrimdv bibi2d albidv spcev fvex eu6 sylibr syl6 ralimdva vex eleq2d eubidv ralbidv exlimiv alimi csn rnex cxp cab cuni eqid biid dfac5lem5 alrimiv dfac3 impbii
```

## dfac0

Source declaration starts at line 112052.

```text
|- ( CHOICE <-> A. x E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) ) )
```

Compressed-proof reference table:

```text
wac wel wa cv wrex wreu wral wex wal weq wb wi dfac7 aceq0 albii bitri
```

## ac8

Source declaration starts at line 118323.

```text
|- ( ( A. z e. x z =/= (/) /\ A. z e. x A. w e. x ( z =/= w -> ( z i^i w ) = (/) ) ) -> E. y A. z e. x E! v v e. ( z i^i y ) )
```

Compressed-proof reference table:

```text
cv c0 wne wral cin wceq wi wa wcel weu wex dfac5 axaci
```

## axac

Source declaration starts at line 118029.

```text
|- E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) )
```

Compressed-proof reference table:

```text
wel wa wex weq wb wal wi wac axac3 dfac0 mpbi spi
```

## axac2

Source declaration starts at line 118015.

```text
|- E. y A. z E. v A. u ( ( y e. x /\ ( z e. y -> ( ( v e. x /\ -. y = v ) /\ z e. v ) ) ) \/ ( -. y e. x /\ ( z e. x -> ( ( v e. z /\ v e. y ) /\ ( ( u e. z /\ u e. y ) -> u = v ) ) ) ) )
```

Compressed-proof reference table:

```text
wel weq wn wa wi wo wal wex wac cv c0 wne wrex wreu wral dfac2a ac3 mpg dfackm mpbi spi
```

## axregs

Source declaration starts at line 577314.

```text
|- ( E. x ph -> E. y ( A. x ( x = y -> ph ) /\ A. z ( z e. y -> -. A. x ( x = z -> ph ) ) ) )
```

Compressed-proof reference table:

```text
cab c0 wne cv wcel wel wa wex wn weq wi wal wsb df-clab sb6 bitri exnal wral zfregs2 df-ral notbii annim anbi2ci df-an con2bii albii alnex bitr2i abn0 anbi12i bitr3i exbii 3bitr2i 3imtr3i
```

## axtco

Source declaration starts at line 602657.

```text
|- E. y ( x e. y /\ A. z ( z e. y -> A. w ( w e. z -> w e. y ) ) )
```

Compressed-proof reference table:

```text
cv csn wss wtr wa wi wal w3a wel vsnex tz9.1 vex snss wral dftr3 df-ss ralbii df-ral 3bitrri anbi12i biimpri 3adant3 eximii
```

The displayed source names axinf and axinf2 establish the two Infinity presentations. The displayed source names dfac5, dfac0, ac8, axac2, and axac establish the Choice presentation routes. Scope and dependencies are given in SET-MATCH-ANALYSIS.md and SET-CANDIDATES.tsv.
