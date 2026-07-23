#!/usr/bin/env python3
"""生成"信任面"总览章 blueprint/src/trust.tex。

动机:剩余假设散落在各节点标签与 Lean docstring 里,读者拼得出但要翻;而且有几项
(hsel、Regularity 强化、R(𝓜) 桥)根本没有节点标签——只从标签生成会漏掉真东西。

做法:清单在本文件里人工维护,但用**双向校验**防止它过期:
  (A) blueprint 里每一个非 [faithful] 标签,都必须被某条清单项覆盖,否则报错;
  (B) 每条清单项引用的 blueprint 标签必须真实存在,否则报错。
于是"改了标签却忘了改总览页"会让脚本直接失败,而不是静默说谎。

用法:python3 tools/gen_trust_surface.py   (在 my_proofs 目录下)
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "blueprint" / "src"
FILES = ["content.tex", "model.tex"]
ENVS = ("lemma", "step", "definition", "faithcheck", "theorem", "proposition")

# ---- 人工维护的信任面清单 ----------------------------------------------------
# covers: 本项覆盖的 (blueprint label, tag) 对;node 为 None 表示"尚无 blueprint 节点"
ITEMS = [
 dict(sev="strengthening", node="def:singleshot", covers=[("def:singleshot","strengthening")],
   title=r"The stopping form is assumed, not derived",
   lean=r"\texttt{DMC.SingleShot.stopping}",
   paper=r"The paper \emph{derives} $U_t=\max\{V_t,\mathbb E[U_{t+1}\mid\mu]\}$ (\texttt{eq:stopping-form}): "
         r"under Assumption~1 the continuation value is the \emph{Snell envelope} of the truncation "
         r"values, via \texttt{lem:stopping-form}.",
   why=r"This is the \textbf{only} remaining assumed item of the model layer proper. Three former "
       r"axioms (\texttt{V\_nonneg}, \texttt{U\_bddAbove}, \texttt{V\_le\_U}) now reduce to it or to "
       r"paper primitives.",
   discharge=r"Formalize the optimal-stopping argument on the belief martingale (least superharmonic "
             r"majorant / Snell envelope) and derive it from Assumption~1."),
 dict(sev="assumed", node="def:selections", covers=[("def:selections","deviation")],
   title=r"Existence of a measurable payoff selection is a hypothesis",
   lean=r"the hypothesis \texttt{hsel} of \texttt{DMC.Paper.U\_mono\_of\_le}, "
        r"\texttt{U\_bddAbove\_of\_bound}, \texttt{toDateValues}",
   paper=r"\texttt{lem:selection-exists}: under Assumption~2(i)--(iii), $\mathcal R_t^{\Gamma_t}$ admits "
         r"a universally measurable selection, by the \textbf{Jankov--von Neumann} selection theorem "
         r"(Kechris, Thm~18.1).",
   why=r"Mathlib has \texttt{AnalyticSet} but \textbf{neither} a \texttt{UniversallyMeasurable} predicate "
       r"\textbf{nor} Jankov--von Neumann (both verified absent). So the paper's proof cannot currently "
       r"be transcribed at all.",
   discharge=r"Either contribute universal measurability $+$ Jankov--von Neumann to Mathlib (a genuine "
             r"library gap, comparable in size to the $\Delta(\Theta)$ work), or formalize the "
             r"finite-strategy case the paper's own Remark singles out, where measurable selection is "
             r"elementary."),
 dict(sev="deviation", node="def:selections", covers=[],
   title=r"\texttt{Sel} uses Borel, not universal, measurability",
   lean=r"\texttt{DMC.Paper.Sel}",
   paper=r"The paper's $\Sel(\mathcal R_t^{\Gamma_t})$ consists of \emph{universally} measurable selections.",
   why=r"Same Mathlib gap as above. The deviation shrinks the feasible set, so the $U_t$ defined here is "
       r"$\le$ the paper's --- i.e.\ it errs in the \textbf{conservative} direction.",
   discharge=r"Same as the previous item."),
 dict(sev="encoding", node="def:singleshot", covers=[("def:singleshot","encoding")],
   title=r"\texttt{condExp} is carried as an abstract operator",
   lean=r"\texttt{DMC.SingleShot.condExp} with \texttt{condExp\_mono}, \texttt{affine\_harmonic}",
   paper=r"$\mathbb E[\varphi(S_{t+1})\mid S_t=\mu]$, the conditional expectation along the posterior process.",
   why=r"Only the two properties actually used downstream are assumed (positivity/monotonicity and "
       r"Bayes-plausibility). Bayes-plausibility is the operative form of the posterior-martingale "
       r"property, which \emph{is} fully proved (paper Lemma~1).",
   discharge=r"Define \texttt{condExp} from the conditional law $\mathbb P_t^\mu$ and the posterior "
             r"process, and derive both properties."),
 dict(sev="encoding", node="def:allocdate", covers=[("def:allocdate","encoding")],
   title=r"The allocation date is an encoding choice",
   lean=r"\texttt{DMC.AllocDate} $=$ \texttt{Option \{n : $\mathbb N$ // 1 $\le$ n\}}",
   paper=r"$\tau\in\{1,2,\dots\}\cup\{\varnothing\}$.",
   why=r"Residual risk is minimal and machine-checked (Faithfulness check on $\emptyset$ vs.\ dates, "
       r"injectivity, and $\tau\ge1$). Note the type is currently \emph{not used} anywhere in the "
       r"development.",
   discharge=r"Nothing outstanding; either put it to use or drop it."),
 dict(sev="weakening", node="def:datevalues", covers=[("def:datevalues","weakening")],
   title=r"\texttt{DateValues} is an interface, weaker than the paper's definitions",
   lean=r"\texttt{DMC.DateValues}",
   paper=r"The paper defines $U_t,V_t$ as suprema; \texttt{DateValues} records only the properties \S3 uses.",
   why=r"No longer postulated: it is \emph{constructed} by \texttt{DMC.Paper.toDateValues} from the "
       r"paper's definitions, and \texttt{toDateValues\_U} checks the \texttt{U} field really is "
       r"$U_t^{\mathcal G}$. Its residual trust reduces to the stopping form above.",
   discharge=r"Nothing beyond the stopping form."),
 dict(sev="strengthening", node=None, covers=[],
   title=r"Regularity is assumed on all of $K$, not just at the prior",
   lean=r"the \texttt{husc} hypothesis of \texttt{DMC.nogain\_belief}; see \texttt{Foundations/Concavification}",
   paper=r"Assumption~3 (\texttt{ass:regularity}) requires $\operatorname{conc}_f[\sup_t U_t]$ to be upper "
         r"semicontinuous \textbf{at the prior $S_0$} only.",
   why=r"Lean assumes upper semicontinuity on the whole of $K$ --- a \emph{stronger} hypothesis, hence a "
       r"\emph{weaker} theorem. Sound, but not the paper's statement. \textbf{Not yet visible in this "
       r"blueprint}: \S3 has no chapter here.",
   discharge=r"Weaken to the one-point condition, or add a \S3 chapter and tag it in situ."),
 dict(sev="gap", node=None, covers=[],
   title=r"The game-theoretic bridge $R(\mathcal M)$ is not formalized",
   lean=r"---",
   paper=r"\texttt{prop:value-representation}: $\sup_{\mathcal M}R(\mathcal M)=(\operatorname{conc}_f[\sup_t "
         r"U_t^{\sigma(Z_t)}])(S_0)$, together with the calendar $\mathcal M$ and $R(\mathcal M)$ themselves.",
   why=r"The main theorem is routed \emph{around} this bridge: no-gain is taken in its post-representation "
       r"equivalent form, which is pure convex analysis. So the bridge does not gate the main result --- "
       r"but the paper's own \S2.2 conclusion is not covered.",
   discharge=r"Formalize the lower bound (branchwise selectors $+$ sequential pasting) and "
             r"\texttt{lem:upper-bound}; both depend on the selection machinery above."),
]

NOT_A_DEFECT = r"""The paper itself never constructs the strategy--belief profiles $\mathcal B_t$, the
sequentially rational Bayesian equilibria $\mathcal E_t$, or the payoff $\pi_t$: it constrains them by
Assumption~2 and works with the induced payoff correspondence $\mathcal R_t^{\Gamma_t}$. The Lean
development stops at exactly the same place. So their absence is \textbf{not} a gap in the
formalization --- it is fidelity to the paper's own abstraction boundary."""

SEV_ORDER = ["strengthening", "assumed", "gap", "deviation", "encoding", "weakening"]
SEV_TITLE = {
 "strengthening": "Strengthening --- Lean assumes something the paper \\emph{derives}",
 "assumed": "Assumed --- a paper lemma taken as a hypothesis",
 "gap": "Gap --- a paper statement with no Lean counterpart yet",
 "deviation": "Deviation --- Lean's notion differs from the paper's",
 "encoding": "Encoding --- a modelling choice, transparency machine-checked",
 "weakening": "Weakening --- Lean assumes \\emph{less} than the paper (safe)",
}

# ---- 校验 --------------------------------------------------------------------
pat = re.compile(r"\\begin\{(" + "|".join(ENVS) + r")\}(?:\[.*?\])?(.*?)\\end\{\1\}", re.S)
found, labels = set(), set()
for fn in FILES:
    t = (SRC / fn).read_text(encoding="utf-8")
    for m in pat.finditer(t):
        body = m.group(2)
        lm = re.search(r"\\label\{([^}]*)\}", body)
        if not lm:
            continue
        labels.add(lm.group(1))
        for tag in set(re.findall(r"\\emph\{\[([a-z]+)\]\}", body)):
            if tag != "faithful":
                found.add((lm.group(1), tag))

covered = {c for it in ITEMS for c in it["covers"]}
errs = []
for pair in sorted(found - covered):
    errs.append(f"blueprint 有残余标签但清单未覆盖: {pair}  → 请在 tools/gen_trust_surface.py 增补")
for pair in sorted(covered - found):
    errs.append(f"清单声称覆盖但 blueprint 里已不存在: {pair}  → 清单已过期")
for it in ITEMS:
    if it["node"] and it["node"] not in labels:
        errs.append(f"清单引用了不存在的 blueprint 标签: {it['node']}")
if errs:
    print("信任面校验失败:"); [print("  -", e) for e in errs]; sys.exit(1)

# ---- 生成 --------------------------------------------------------------------
out = [r"""% 由 tools/gen_trust_surface.py 生成 —— 请勿手改。
% 内容与 blueprint 各节点的 [tag] 双向校验一致(不一致则生成脚本报错)。

\chapter{Trust surface: what is still assumed}

Green on this site means the Lean \textbf{kernel checked a proof against a stated Lean proposition}.
It never means ``this matches the paper''. That second step is a human translation, and wherever it
is not fully discharged, the residue is listed \emph{here} --- in one place, rather than scattered
across nodes and docstrings.

This chapter is generated from the faithfulness tags on the nodes, and the generator \textbf{fails}
if a tag exists that this list does not cover, or if this list refers to a tag that no longer exists.
So it cannot silently go out of date.

\medskip
\noindent\textbf{Not counted as gaps.} """ + NOT_A_DEFECT + "\n"]

for sev in SEV_ORDER:
    items = [it for it in ITEMS if it["sev"] == sev]
    if not items:
        continue
    out.append("\n\\section*{" + SEV_TITLE[sev] + "}\n")
    for it in items:
        where = (f"Blueprint: \\ref{{{it['node']}}}. " if it["node"]
                 else r"\textbf{No blueprint node yet.} ")
        out.append(
            "\\begin{itemize}\n"
            f"  \\item[] \\textbf{{{it['title']}}}\\\\\n"
            f"  {where}Lean: {it['lean']}.\n"
            f"  \\par\\smallskip\\emph{{What the paper says.}} {it['paper']}\n"
            f"  \\par\\smallskip\\emph{{Why it is not discharged.}} {it['why']}\n"
            f"  \\par\\smallskip\\emph{{What would discharge it.}} {it['discharge']}\n"
            "\\end{itemize}\n")

(SRC / "trust.tex").write_text("".join(out), encoding="utf-8")
print(f"已生成 blueprint/src/trust.tex:{len(ITEMS)} 条,覆盖 {len(found)} 个残余标签,双向校验通过")
