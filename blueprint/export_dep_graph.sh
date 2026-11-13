#!/usr/bin/env bash
# Rebuild the web blueprint, inject an inline SVG fallback into dep_graph_document.html
# so it works over file:// without WASM CORS errors, and export report/blueprint_dep_graph.pdf.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/anaconda3/envs/leanblueprint/bin:/Library/TeX/texbin:/opt/homebrew/bin:/usr/local/bin:$PATH"
(cd blueprint && leanblueprint web)
python3 - <<'PY'
import re, subprocess

html_path = 'blueprint/web/dep_graph_document.html'
s = open(html_path, encoding='utf-8').read()
m = re.search(r'renderDot\(`(.*?)`\)', s, re.S)
dot_raw = m.group(1)

dot = dot_raw.replace(
    'bgcolor=transparent',
    'bgcolor=white, nodesep=0.08, ranksep=1.15, margin=0',
    1
).replace(
    'penwidth=1.8',
    'penwidth=1.8, fontsize=20, margin="0.04,0.02"',
    1
)
open('blueprint/dep_graph.dot', 'w', encoding='utf-8').write(dot)

# Render inline SVG so opening file:///.../dep_graph_document.html works without a local HTTP server
svg_raw = subprocess.check_output(['dot', '-Tsvg', 'blueprint/dep_graph.dot'], text=True)
svg_match = re.search(r'(<svg\b.*</svg>)', svg_raw, re.S)
if svg_match:
    svg_elem = svg_match.group(1)
    svg_elem = re.sub(
        r'<svg\b([^>]*)>',
        r'<svg\1 style="width: 100%; height: 100%; max-width: 100%; max-height: 88vh; display: block; margin: 0 auto;">',
        svg_elem,
        count=1,
    )
    s = s.replace('<div id="graph"></div>', f'<div id="graph">\n{svg_elem}\n</div>', 1)
    # Also attach interactive() immediately on DOM load so clicking nodes works even if WASM fails on file://
    s = s.replace('function interactive() {', 'document.addEventListener("DOMContentLoaded", function() { try { interactive(); } catch (e) {} });\nfunction interactive() {', 1)
    s = s.replace('graphContainer.graphviz({useWorker: true})', 'if (window.location.protocol !== "file:") graphContainer.graphviz({useWorker: false})', 1)
    open(html_path, 'w', encoding='utf-8').write(s)
PY
mkdir -p report
dot -Tpdf blueprint/dep_graph.dot -o report/blueprint_dep_graph.pdf
echo "Wrote report/blueprint_dep_graph.pdf and injected inline SVG into blueprint/web/dep_graph_document.html"
