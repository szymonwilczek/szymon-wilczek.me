import temml from "temml";
import { fromHtml } from "hast-util-from-html";
import { visit } from "unist-util-visit";
import temmlCss from "temml/dist/Temml-Local.css?raw";
import { DISPLAY_MATH_CLASS, MATH_CLASS } from "./org-pipeline";

const FONT_FACE_RULE = /@font-face\s*{[^}]*}/g;
export const mathStyles = temmlCss.replace(FONT_FACE_RULE, "").trim();

export function hasMath(html: string): boolean {
  return html.includes("<math");
}

export function rehypeTemml() {
  return (tree: any) => {
    visit(tree, "element", (node: any, index: number | undefined, parent: any) => {
      const classes = node.properties?.className;
      if (!Array.isArray(classes) || !classes.includes(MATH_CLASS)) return;
      if (!parent || typeof index !== "number") return;

      const latex = node.children.map((child: any) => child.value ?? "").join("");
      const mathml = temml.renderToString(latex, {
        displayMode: classes.includes(DISPLAY_MATH_CLASS),
        throwOnError: true,
      });
      parent.children.splice(index, 1, ...fromHtml(mathml, { fragment: true }).children);
    });
  };
}
