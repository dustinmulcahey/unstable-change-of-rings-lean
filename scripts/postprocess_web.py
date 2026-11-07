#!/usr/bin/env python3
"""Post-process Lean Blueprint HTML files so that:
1. Every `ThesisLean.*` declaration link points directly to its exact file and line
   on GitHub (`https://github.com/dustinmulcahey/unstable-change-of-rings-lean/blob/main/...#L...`).
2. `paper/unstable_change_of_rings.pdf` and `blueprint/print/blueprint.pdf` are copied into
   `blueprint/web/` and linked in the navigation sidebar.
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
        '<li ><a href="blueprint.pdf">Blueprint (PDF)</a></li>'
    )

    for html_path in sorted(glob.glob(os.path.join(WEB_DIR, "*.html"))):
        with open(html_path, "r", encoding="utf-8") as f:
            content = f.read()

        def repl(match):
            decl = match.group(1)
            return decl_map.get(decl, f"{REPO_URL}/ThesisLean")

        content = link_re.sub(repl, content)
        if "unstable_change_of_rings.pdf" not in content:
            content = content.replace(
                '<li ><a href="dep_graph_document.html">Dependency graph</a></li>',
                extra_nav,
            )

        with open(html_path, "w", encoding="utf-8") as f:
            f.write(content)


def main():
    decl_map = index_lean_declarations()
    print(f"Indexed {len(decl_map)} Lean declarations across ThesisLean/*.lean")
    process_html_files(decl_map)

    paper_pdf = os.path.join(ROOT_DIR, "paper", "unstable_change_of_rings.pdf")
    blueprint_pdf = os.path.join(ROOT_DIR, "blueprint", "print", "blueprint.pdf")
    if os.path.exists(paper_pdf):
        shutil.copy2(paper_pdf, os.path.join(WEB_DIR, "unstable_change_of_rings.pdf"))
    if os.path.exists(blueprint_pdf):
        shutil.copy2(blueprint_pdf, os.path.join(WEB_DIR, "blueprint.pdf"))

    nojekyll = os.path.join(WEB_DIR, ".nojekyll")
    with open(nojekyll, "w", encoding="utf-8") as f:
        f.write("")
    print("Post-processed blueprint/web/ successfully.")


if __name__ == "__main__":
    main()
