#!/usr/bin/env python3
"""Post-process Lean Blueprint HTML files so that:
1. Every `ThesisLean.*` declaration link points directly to its exact file and line
   on GitHub (`https://github.com/dustinmulcahey/unstable-change-of-rings-lean/blob/main/...#L...`).
2. `paper/unstable_change_of_rings.pdf`, `blueprint/print/blueprint.pdf`, and
   `paper/changeofcomonads_original_thesis.pdf` are copied into `blueprint/web/`
   and linked in the navigation sidebar and landing page (`index.html`).
3. `.nojekyll` is created in `blueprint/web/` for GitHub Pages.
"""

import glob
import os
import re
import shutil

REPO_URL = "https://github.com/dustinmulcahey/unstable-change-of-rings-lean/blob/main"
ROOT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN_DIR = os.path.join(ROOT_DIR, "ThesisLean")
WEB_DIR = os.path.join(ROOT_DIR, "blueprint", "web")

INDEX_INTRO_HTML = """
<div class="project-overview" style="margin: 1.5rem 0 2rem 0; padding: 1.25rem 1.5rem; background: #f8fafc; border-left: 4px solid #195fa5; border-radius: 6px; line-height: 1.6;">
  <p style="margin-top: 0;">
    This site is the interactive <strong>Lean 4 Blueprint</strong> for Dustin Mulcahey's Ph.D. thesis,
    <em>&ldquo;An unstable variant of the Morava Change of Rings theorem for \\(K(n)\\) theory&rdquo;</em>
    (The Graduate Center, CUNY; Advisors: Robert Thompson &amp; Martin Bendersky).
    Every categorical definition, proposition, and theorem in Chapters 2 and 3 has been completely formalized and verified with zero <code>sorry</code> axioms in Lean 4 + Mathlib4.
  </p>
  <p style="margin-bottom: 0.5rem;"><strong>Documents &amp; Interactive Views:</strong></p>
  <ul style="margin-top: 0.25rem; margin-bottom: 0;">
    <li><a href="dep_graph_document.html"><strong>Interactive Dependency Graph</strong></a> &mdash; visual logical dependency graph (all nodes verified in green; click any node to inspect its statement and Lean proof)</li>
    <li><a href="unstable_change_of_rings.pdf"><strong>Journal-Style <code>amsart</code> Paper (PDF)</strong></a> &mdash; self-contained article version with <code>[Lean 4]</code> badges and a complete theorem-to-Lean concordance table</li>
    <li><a href="blueprint.pdf"><strong>Blueprint Print Edition (PDF)</strong></a> &mdash; printable PDF version of this blueprint</li>
    <li><a href="changeofcomonads_original_thesis.pdf"><strong>Original CUNY Ph.D. Thesis (PDF)</strong></a> &mdash; original dissertation typeset in <code>CUNY_PhD.cls</code></li>
    <li><a href="https://github.com/dustinmulcahey/unstable-change-of-rings-lean"><strong>GitHub Repository (<code>dustinmulcahey/unstable-change-of-rings-lean</code>)</strong></a> &mdash; Lean 4 source code (<code>ThesisLean/</code>), LaTeX sources, and build instructions</li>
  </ul>
</div>
"""


def index_lean_declarations():
    decl_map = {}
    ns_re = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)")
    end_re = re.compile(r"^\s*end\s+([A-Za-z0-9_.]+)")
    decl_re = re.compile(
        r"^\s*(?:noncomputable\s+|protected\s+|private\s+)*"
        r"(?:def|abbrev|lemma|theorem|structure|class|inductive)\s+([A-Za-z0-9_'.]+)"
    )

    for path in sorted(glob.glob(os.path.join(LEAN_DIR, "*.lean"))):
        rel_path = os.path.relpath(path, ROOT_DIR).replace("\\", "/")
        ns_stack = []
        with open(path, "r", encoding="utf-8") as f:
            for lineno, line in enumerate(f, start=1):
                m_ns = ns_re.match(line)
                if m_ns:
                    for part in m_ns.group(1).split("."):
                        ns_stack.append(part)
                    continue
                m_end = end_re.match(line)
                if m_end:
                    parts = m_end.group(1).split(".")
                    for _ in parts:
                        if ns_stack:
                            ns_stack.pop()
                    continue
                m_decl = decl_re.match(line)
                if m_decl:
                    name = m_decl.group(1)
                    full_name = ".".join(ns_stack + [name])
                    decl_map[full_name] = f"{REPO_URL}/{rel_path}#L{lineno}"
    return decl_map


def process_html_files(decl_map):
    old_prefix = "https://leanprover-community.github.io/mathlib4_docs/find/#doc/"
    link_re = re.compile(re.escape(old_prefix) + r"(ThesisLean\.[A-Za-z0-9_'.]+)")

    extra_nav = (
        '<li ><a href="dep_graph_document.html">Dependency graph</a></li>\n'
        '<li ><a href="unstable_change_of_rings.pdf">Paper (PDF)</a></li>\n'
        '<li ><a href="blueprint.pdf">Blueprint (PDF)</a></li>\n'
        '<li ><a href="changeofcomonads_original_thesis.pdf">Original Thesis (PDF)</a></li>'
    )

    for html_path in sorted(glob.glob(os.path.join(WEB_DIR, "*.html"))):
        with open(html_path, "r", encoding="utf-8") as f:
            content = f.read()

        def repl(match):
            decl = match.group(1)
            return decl_map.get(decl, f"{REPO_URL}/ThesisLean")

        content = link_re.sub(repl, content)
        if "changeofcomonads_original_thesis.pdf" not in content:
            if '<li ><a href="unstable_change_of_rings.pdf">Paper (PDF)</a></li>' in content:
                content = content.replace(
                    '<li ><a href="blueprint.pdf">Blueprint (PDF)</a></li>',
                    '<li ><a href="blueprint.pdf">Blueprint (PDF)</a></li>\n'
                    '<li ><a href="changeofcomonads_original_thesis.pdf">Original Thesis (PDF)</a></li>',
                )
            else:
                content = content.replace(
                    '<li ><a href="dep_graph_document.html">Dependency graph</a></li>',
                    extra_nav,
                )

        if os.path.basename(html_path) == "index.html" and "project-overview" not in content:
            content = content.replace(
                "</div> <!--main-text -->",
                INDEX_INTRO_HTML + "\n</div> <!--main-text -->",
            )

        with open(html_path, "w", encoding="utf-8") as f:
            f.write(content)


def main():
    decl_map = index_lean_declarations()
    print(f"Indexed {len(decl_map)} Lean declarations across ThesisLean/*.lean")
    process_html_files(decl_map)

    pdfs = [
        (os.path.join(ROOT_DIR, "paper", "unstable_change_of_rings.pdf"), "unstable_change_of_rings.pdf"),
        (os.path.join(ROOT_DIR, "blueprint", "print", "blueprint.pdf"), "blueprint.pdf"),
        (
            os.path.join(ROOT_DIR, "paper", "changeofcomonads_original_thesis.pdf"),
            "changeofcomonads_original_thesis.pdf",
        ),
    ]
    for src, dst_name in pdfs:
        if os.path.exists(src):
            shutil.copy2(src, os.path.join(WEB_DIR, dst_name))

    nojekyll = os.path.join(WEB_DIR, ".nojekyll")
    with open(nojekyll, "w", encoding="utf-8") as f:
        f.write("")
    print("Post-processed blueprint/web/ successfully.")


if __name__ == "__main__":
    main()
