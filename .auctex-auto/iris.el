(TeX-add-style-hook
 "iris"
 (lambda ()
   (setq TeX-command-extra-options
         "-shell-escape")
   (TeX-run-style-hooks
    "tikz"
    "scalerel"
    "array"
    "dashbox"
    "tensor"
    "xparse"
    "xstring"
    "mathtools")
   (TeX-add-symbols
    '("anglebracket" ["argument"] 1)
    '("curlybracket" ["argument"] 1)
    '("bracket" ["argument"] 3)
    '("fgmapsto" ["argument"] 0)
    '("fmapsto" ["argument"] 0)
    '("mincl" ["argument"] 0)
    '("judgment" ["argument"] 1)
    '("disj" ["argument"] 0)
    '("semKtype" 3)
    '("semEtype" 3)
    '("semVtype" 3)
    '("IDisj" 2)
    '("IConj" 2)
    '("IPersistent" 1)
    '("IName" 1)
    '("semtyped" 4)
    '("ctxtyped" 7)
    '("seqtyped" 4)
    '("cooptyped" 4)
    '("typed" 4)
    '("op" 1)
    '("CFork" 1)
    '("Fork" 1)
    '("Cas" 3)
    '("Proj" 1)
    '("Inj" 1)
    '("lvar" 1)
    '("langghost" 1)
    '("langkws" 1)
    '("textlang" 1)
    '("stsftrans" 1)
    '("stsfstep" 1)
    '("authfragSub" 1)
    '("authfullSub" 1)
    '("Some" 1)
    '("option" 1)
    '("hstep" 1)
    '("physatomic" 1)
    '("persistent" 1)
    '("timeless" 1)
    '("triple" 5)
    '("hoarescalebox" 2)
    '("hoaresizebox" 1)
    '("ownPhys" 1)
    '("ownM" 1)
    '("ownGGhost" 1)
    '("ownGhost" 2)
    '("knowInv" 2)
    '("namecl" 1)
    '("textlog" 1)
    '("mcore" 1)
    '("mcarp" 1)
    '("mcar" 1)
    '("textmon" 1)
    '("typedsection" 2)
    '("sembox" 1)
    '("Sem" 1)
    '("nequivB" 1)
    '("nequivset" 2)
    '("notnequiv" 1)
    '("wtt" 2)
    '("wsat" 3)
    '("textdom" 1)
    '("subst" 3)
    '("finpset" 1)
    '("psetdown" 1)
    '("pset" 1)
    '("recordComp" 2)
    '("record" 1)
    '("set" 1)
    '("setComp" 2)
    "nat"
    "asts"
    "Sep"
    "pord"
    "dplus"
    "upclose"
    "ALT"
    "spac"
    "any"
    "pfn"
    "fpfn"
    "la"
    "ra"
    "Ra"
    "Lra"
    "monra"
    "nfn"
    "eqdef"
    "bnfdef"
    "dom"
    "cod"
    "chain"
    "Func"
    "wIso"
    "rs"
    "rsB"
    "rss"
    "pres"
    "wld"
    "ghostRes"
    "wsatpre"
    "latert"
    "latertinj"
    "SProp"
    "UPred"
    "mProp"
    "iProp"
    "iPreProp"
    "Wld"
    "Res"
    "State"
    "Val"
    "Var"
    "Ectx"
    "Loc"
    "cofe"
    "cofeB"
    "COFEs"
    "iFunc"
    "fix"
    "monoid"
    "mval"
    "melt"
    "meltB"
    "meltC"
    "melts"
    "meltsB"
    "f"
    "munit"
    "mtimes"
    "mupd"
    "CMRAs"
    "Sig"
    "SigType"
    "SigFn"
    "SigAx"
    "sigtype"
    "sigfn"
    "sigax"
    "type"
    "typeB"
    "var"
    "varB"
    "varC"
    "term"
    "termB"
    "vctx"
    "pfctx"
    "prop"
    "propB"
    "propC"
    "pprop"
    "ppropB"
    "pred"
    "predB"
    "predC"
    "gname"
    "iname"
    "mask"
    "namesp"
    "proves"
    "provesCoq"
    "provesIff"
    "wand"
    "gmapsto"
    "later"
    "always"
    "pure"
    "vsWand"
    "infinite"
    "Prop"
    "Pred"
    "TRUE"
    "FALSE"
    "TLam"
    "expr"
    "val"
    "valB"
    "pstate"
    "step"
    "coopstep"
    "seqstep"
    "tpstep"
    "elctx"
    "lctx"
    "reduces"
    "coopreduces"
    "seqreduces"
    "toval"
    "ofval"
    "atomic"
    "red"
    "Lang"
    "tpool"
    "cfg"
    "None"
    "agm"
    "aginj"
    "fracm"
    "exm"
    "exinj"
    "authm"
    "authfull"
    "authfrag"
    "AuthInv"
    "Auth"
    "oneshotm"
    "ospending"
    "osshot"
    "STSCtx"
    "STSSt"
    "STSclsd"
    "STSauth"
    "STSfrag"
    "STSS"
    "STST"
    "STSL"
    "stsstep"
    "ststrans"
    "mapstoprop"
    "lvarA"
    "lvarB"
    "lvarC"
    "loc"
    "JustFork"
    "JustCFork"
    "Yield"
    "deref"
    "callccop"
    "throwop"
    "empctx"
    "fold"
    "unfold"
    "unop"
    "binop"
    "Plus"
    "Minus"
    "Mult"
    "Eq"
    "Lt"
    "TT"
    "tvar"
    "tvarB"
    "TVar"
    "Expr"
    "typ"
    "typB"
    "Tunit"
    "Tbool"
    "Tnat"
    "Tarr"
    "Tenv"
    "env"
    "coopvdash"
    "seqvdash"
    "ctxrefines"
    "ctxequiv"
    "logrefines"
    "ipat"
    "IAnom"
    "IDrop"
    "IAnomPure"
    "IFalse"
    "iFrame"
    "app"
    "reverse"
    "semenv"
    "obrefines"
    "crossobrefines"
    "All"
    "Exists"
    "Ret"
    "MU"
    "Lam"
    "fill"
    "Let"
    "If"
    "Else"
    "Ref"
    "Rec"
    "Skip"
    "Assert"
    "True"
    "False"
    "Match"
    "MatchML"
    "MatchMLL"
    "MatchS"
    "gets"
    "cont"
    "callcc"
    "throw"
    "NewProph"
    "Resolve"
    "Tall"
    "Tmu"
    "Tref"
    "Tcont")
   (LaTeX-add-environments
    '("returnanother" LaTeX-env-args ["argument"] 5)
    '("inbox" LaTeX-env-args ["argument"] 0))
   (LaTeX-add-xparse-macros
    '("wpre" "m O{} m")
    '("clwpre" "m O{} m")
    '("boxedassert" "O{} m o")
    '("vsGen" "O{} m O{}")
    '("vs" "O{} O{}")
    '("vsL" "O{} O{}")
    '("vsE" "O{} O{}")
    '("pvs" "O{} O{}")
    '("vsW" "O{} O{}")
    '("upd" "")
    '("hoare" "m m m O{}")
    '("customhoare" "m m m m O{}")
    '("clhoare" "m m m O{}")
    '("hoareV" "O{c} m m m O{}")
    '("hoareHV" "O{c} m m m O{}")
    '("clhoareV" "O{c} m m m O{}")
    '("clhoareHV" "O{c} m m m O{}")))
 :latex)

