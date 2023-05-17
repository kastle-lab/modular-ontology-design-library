import os
import re
import glob
import argparse

import rdflib
from rdflib import RDF, RDFS, OWL

# =======================
# rdflib helper functions


def get_namespace(prefix, graph):
    '''Iterate through the namespaces and return the match'''
    for p, ns in graph.namespaces():
        if p == prefix:
            return ns
    return rdflib.term.URIRef("https://missing.com#missing")


def get_predicate(prefix, predicate, graph):
    '''Construct a URI for a predicate given the pred_name, prefix, and graph'''
    ns = get_namespace(prefix, graph)
    return ns + predicate

# =======================
# LaTeX rendering


def tsf(x):
    '''Render in sans serif font'''
    return "\\textsf{" + x + "} "


# Shortcuts for math notations
sc = "&\\sqsubseteq "
forall = "\\forall "
exists = "\\exists "
minz = "\\lte 0"
func = "\\lte 1"
inv = "^-"

# =======================
# Generate figure code


def generate_figure_code(filename, caption="Empty Caption", label=None):
    # Create filename path
    filename = "{resources/" + filename + "}"
    # Generate the label
    if label == None:
        label = get_label(filename)
    if label.startswith("fig:"):
        label = label.replace("fig:", "")
    label = "{fig:" + label + "}"
    # Wrap Caption
    caption = "{" + caption + "}"
    # Construct figure code
    figure_lines = list()
    figure_lines.append("\\begin{figure}[h!]")
    figure_lines.append("  \\begin{center}")
    figure_lines.append("    \\includegraphics[width=\\textwidth]{}".format(filename))
    figure_lines.append("  \\end{center}")
    figure_lines.append("  \\caption{}".format(caption))
    figure_lines.append("  \\label{}".format(label))
    figure_lines.append("\\end{figure}\n")
    # Separate by new lines
    figure = '\n'.join(figure_lines)
    # And return
    return figure

# =======================
# Generation of common elements in subsections


def generate_label(label):
    label = label.replace(" ", "-").lower()

    return label


def generate_header(section_name, label=None):
    if label is None:
        label = generate_label(section_name)

    header = "%"*35 + "\n"
    header += "\\subsection{" + section_name + "}\n"
    header += "\\label{ssec:" + label + "}\n"
    header += "%"*10 + "\n"

    return header

# =======================
# Subsection generators


def generate_overview(g):
    # Pattern name
    hPN = get_predicate("opla-core", "hasPatternName", g)
    # There should only ever be one....
    pattern_name = [str(o) for s, p, o in g.triples((None, hPN, None))][0]
    # Create Header
    overview = generate_header("Overview")
    # Begin Content Generation
    # =======================
    # Insert Overview Text
    overview += "I am the overview.\n"
    # End Overview Text
    # =======================
    # Insert top level schema Diagram
    # Find if there is a schema diagram
    # get node representing this ontology
    # get predicate for schema diagram file name
    # TODO: this currently assumes there is only 1 schema diagram
    hSDF = get_predicate("opla-sd", "hasSchemaDiagramFileName", g)
    schema_diagram = [str(o) for s, p, o in g.triples((None, hSDF, None))]
    if len(schema_diagram) == 0:
        return overview

    for o in schema_diagram:
        filename = str(o)
        caption = f"The schema diagram for the {pattern_name}."
        figure_code = generate_figure_code(filename, caption, label="ov-diagram")
        overview += "\n" + figure_code

    # End subsection
    overview += "\n"
    return overview


def generate_cqs(g):
    # Create Header
    cqs = generate_header("Competency Questions", label="cqs")
    # Begin Content Generation
    # Create the predicate URI for the opla-cp:hasCompetencyQuestion
    hCQ = get_predicate("opla-cp", "hasCompetencyQuestion", g)
    questions = [str(o) for s, p, o in g.triples((None, hCQ, None))]
    questions.sort()
    # Now for each triple in the pattern, get the competency question
    # Note: g.triples() does not guarantee order
    if len(questions) == 0:
        cqs += "There are no competency questions documented for this pattern."
        cqs += "\n"
        return cqs

    cqs += "\\begin{enumerate}[\\phantom{CQ }CQ 1.]\n"
    for q in questions:
        cqs += "\t\\item "
        cqs += q
        cqs += "\n"
    cqs += "\\end{enumerate}"
    # End subsection
    cqs += "\n"
    return cqs


def generate_usecases(g):
    # Create Header
    usecases = generate_header("Use Cases")
    # Begin Content Generation
    # Create the predicate URI for the opla-cp:addressesScenario
    aS = get_predicate("opla-cp", "addressesScenario", g)
    # Now for each triple in the pattern, get the scenarios (usecases)
    scenarios = [str(o) for s, p, o in g.triples((None, aS, None))]
    scenarios.sort()
    # Note: g.triples() is a generator, so there is no easy way to
    #   generate len hence this weird conditional workaround to
    #   leave a token message if no competency questions are found.
    # Note: g.triples() does not guarantee order
    scenarios_is_empty = True
    first = True
    for o in scenarios:
        if first:
            scenarios_is_empty = False
            first = False
            usecases += "These are the usecases!\n"

        usecase = str(o)
        title, *text = usecase.split("\n")
        text = "\n".join(text)
        usecases += "\n\\subsubsection{" + title + "}\n"
        usecases += text + "\n"
    # This is down here because the scenarios is actually a generator
    # not an iterable, thus we can't check len earlier than the loop
    if scenarios_is_empty:
        usecases += "There are no usecases documented for this pattern."
    # End subsection
    return usecases


def generate_axiomatization(lines):
    axiomatization = ""  # string for holding the axiomatization and explanations
    axioms = list()
    explanations = list()

    for line in lines:
        if line == '':
            continue
        s, p, o, *args = line.strip().split(" ")

        if p == "subclass":
            lhs = tsf(s)
            rhs = tsf(o)
            subclass = lhs + sc + rhs
            axioms.append(subclass)
            explanations.append("Subclass")
            continue

        # Write Scoped Range
        lhs = tsf(s)
        rhs = forall + tsf(p + "." + o)
        scoped_range = lhs + sc + rhs
        axioms.append(scoped_range)
        explanations.append("Scoped Range")

        # Write Scoped Domain
        lhs = exists + tsf(p + "." + s)
        rhs = tsf(o)
        scoped_domain = lhs + sc + rhs
        axioms.append(scoped_domain)
        explanations.append("Scoped Domain")

        if len(args) > 0:
            for arg in args:
                if arg == "existential":
                    lhs = tsf(s)
                    rhs = exists + tsf(p + "." + s)
                    existential = lhs + sc + rhs
                    axioms.append(existential)
                    explanations.append("Existential")
                elif arg == "inverse-existential":
                    lhs = tsf(o)
                    # rhs = exists + tsf(p) + inv + tsf("." + o)
                    rhs = exists + tsf(p)[:-1]+"^-" + tsf("." + o)
                    inverse_existential = lhs + sc + rhs
                    axioms.append(inverse_existential)
                    explanations.append("Inverse Existential")

    axiomatization += "\\subsubsection{Axioms}\n"
    axiomatization += "\\begin{align}\n"
    for axiom in axioms:
        axiomatization += "  " + axiom
        if axiom != axioms[-1]:
            axiomatization += "\\\\\n"
    axiomatization += "\\end{align}\n\n"

    axiomatization += "\\subsubsection{Explanations}\n"
    axiomatization += "\\begin{enumerate}\n"
    for explanation in explanations:
        axiomatization += "  \\item " + explanation + "\n"
    axiomatization += "\\end{enumerate}"

    return axiomatization


def generate_formalization(g):
    # Create Header
    formalization = generate_header("Formalization")
    # Begin Content Generation
    hC = get_predicate("opla-sd", "hasConnections", g)
    connections = None

    # There should only ever be one of these
    for s, p, o in g.triples((None, hC, None)):
        connections = str(o)

    if connections is None:
        formalization += "There is currently no formalization documented for this pattern."
        formalization += "\n"
        return formalization

    lines = o.split("\n")
    formalization += generate_axiomatization(lines)

    # End subsection
    formalization += "\n"
    return formalization


def generate_submodules(g):
    # Create Header
    submodules = generate_header("Submodules")
    # Begin Content Generation
    submodules += "Submodule detection not yet supported."
    # End subsection
    submodules += "\n"
    return submodules


def generate_views(g):
    # Pattern name
    hPN = get_predicate("opla-core", "hasPatternName", g)
    # There should only ever be one....
    pattern_name = [str(o) for s, p, o in g.triples((None, hPN, None))][0]
    # Create Header
    views = generate_header("Views")
    # Begin Content Generation
    # Generate Figure
    hSD = get_predicate("opla-sd", "hasShortcutDiagramFileName", g)
    shortcut_diagrams = [str(o) for s, p, o in g.triples((None, hSD, None))]
    # There should only be one at this stage.
    # TODO: retool annotations to link specific shortcuts with a specific view
    for shortcut_diagram in shortcut_diagrams:
        caption = f"Schema diagram displaying shortcuts for {pattern_name} (red arrows)."
        figure_code = generate_figure_code(shortcut_diagram, caption, label="sc-diagram")
        views += figure_code

    hSF = get_predicate("opla-core", "hasShortcutFor", g)
    shortcuts = [str(o) for s, p, o in g.triples((None, hSF, None))]
    if len(shortcuts) == 0:
        views += "There are no views documented for this pattern."
        views += "\n"
    else:
        views += "The shortcuts are as follows."
        views += "\\begin{align}\n"
        for shortcut in shortcuts:
            preds = shortcut.split(" ")
            lhs = [tsf(p) for p in preds[:-1]]
            rhs = tsf(preds[-1])

            shortcut_string = " \\circ ".join(lhs) + sc + rhs
            if shortcut != shortcuts[-1]:
                shortcut_string += "\n"
            views += shortcut_string
        views += "\\end{align}\n"
    # End subsection
    views += "\n"

    return views


def generate_entanglements(g):
    # Create Header
    entanglements = generate_header("Entanglements")
    # Begin Content Generation
    hE = get_predicate("opla-core", "hasEntanglement", g)
    ents = [str(o) for s, p, o in g.triples((None, hE, None))]
    if len(ents) == 0:
        entanglements += "There are no entanglements documented for this pattern."
        entanglements += "\n"
        return entanglements
    # End subsection
    entanglements += "\n"
    return entanglements


def generate_examples(g):
    # Pattern name
    hPN = get_predicate("opla-core", "hasPatternName", g)
    # There should only ever be one....
    pattern_name = [str(o) for s, p, o in g.triples((None, hPN, None))][0]
    # Create Header
    examples = generate_header("Examples")
    # Begin Content Generation
    # Insert Example figure
    hEDF = get_predicate("opla-sd", "hasExampleDiagramFileName", g)
    example_diagrams = [str(o) for s, p, o in g.triples((None, hEDF, None))]
    if len(example_diagrams) == 0:
        examples += "There are no examples documented for this pattern."
        examples += "\n"
        return examples

    for example_diagram in example_diagrams:
        filename = example_diagram
        caption = f"An example ``instantiation'' of the {pattern_name} in schema diagram form."
        figure_code = generate_figure_code(filename, caption, label="ex-diagram")
        examples += figure_code
    # Insert Text
    examples += "\\begin{verbatim}\n"
    examples += "Example Triples\n"
    examples += "\\end{verbatim}\n"
    # End subsection
    return examples


def generate_remarks(g):
    pass


def generate_known_issues(g):
    pass


# ======================
# Set up
section_generators = [generate_overview, generate_cqs, generate_usecases, generate_formalization,
                      generate_submodules, generate_views, generate_entanglements, generate_examples]
section_names = ["overview", "cqs", "usecases", "formalization", "submodules", "views", "entanglements", "examples"]
section_generator_map = {key: value for (key, value) in zip(section_names, section_generators)}
# ======================


def generate_preamble(contributors, acknowledgement, output_dir):
    preamble_start = """\\setlrmarginsandblock{1in}{1in}{*}
\\setulmarginsandblock{1in}{1in}{*}
\\checkandfixthelayout

\\usepackage{graphicx}

\\usepackage{enumerate,xcolor,soul,framed}

\\usepackage{mathtools,amssymb}
\\allowdisplaybreaks[1]
\\usepackage{url}
\\usepackage{paralist}
\\usepackage{hyperref}
\\usepackage{parskip}
\\tightlists

\\usepackage{textcomp}
\\usepackage[T1]{fontenc}
\\usepackage{palatino}
\\linespread{1.025}
\\let\\oldtextlangle\\textlangle
\\renewcommand{\\textlangle}{{\\fontfamily{pxr}\\selectfont\\oldtextlangle}}
\\let\\oldtextrangle\\textrangle
\\renewcommand{\\textrangle}{{\\fontfamily{pxr}\\selectfont\\oldtextrangle}}


\\setverbatimfont{\\sffamily}

\\renewcommand{\\theequation}{\\arabic{equation}}

\\newlength{\\drop}% for my convenience
\\newcommand*{\\titleBWF}{\\begingroup
\\drop = 0.1\\textheight
\\parindent=0pt
\\vspace*{\\drop}
{\\Huge\\bfseries Ontology Design Patterns for Modeling Events, Places, \\& Relationships}\\\\
[\\baselineskip]

\\vspace*{0.5\\drop}
{\\Large {\itshape Contributors:}}\\\\\n"""
    # Sort the contributors by space delineated last name
    # Hopefully no one has two last names
    contributors = list(contributors)

    def getKey(item):
        return item.split(" ")[-1]
    contributors = sorted(contributors, key=getKey)
    # Write the contributors
    preamble_contributors = ""
    for contributor in contributors:
        preamble_contributors += "{\\large{\\scshape ~}}\\\\\n".replace("~", contributor)
    preamble_contributors = preamble_contributors[:-1] + "[\\baselineskip]\n\n"
    preamble_date = """{\\large {\\itshape Document Date:} \\today}

\\vfill\n\n"""
    preamble_end = """\\endgroup}

\\setsecnumdepth{subsubsection}
\\maxtocdepth{section}
\\chapterstyle{tandh}
\\pagestyle{simple}"""

    with open(f"{output_dir}/preamble.tex", "w") as output:
        preamble = preamble_start + preamble_contributors + preamble_date
        preamble += "{" + acknowledgement + "}\n\n" + preamble_end
        output.write(preamble)


def generate_pattern_documentation(section_order, filename, output_dir):
    g = rdflib.Graph()
    g.parse(filename, format="ttl")

    pattern_name = ""
    hPN = get_predicate("opla-core", "hasPatternName", g)
    for s, p, o in g.triples((None, hPN, None)):
        pattern_name = str(o)

    documentation = ""
    for section in section_order:
        documentation += section_generator_map[section](g) + "\n"

    with open(f"{output_dir}/patterns.tex", "a") as output:
        output.write("%"*35+"\n")
        output.write("\\section{" + pattern_name + "}\n")
        output.write("\\label{sec:" + generate_label(pattern_name) + "}\n")
        output.write(documentation)
        output.write("%"*35+"\n")
        output.write("%"*11 + " End Section " + "%"*11+"\n")
        output.write("%"*35+"\n")
        output.write("\n")

    # Finally, get contributors for this pattern
    creators = set()
    creatorPred = get_predicate("dc", "creator", g)
    creator_list = [str(o) for s, p, o in g.triples((None, creatorPred, None))]
    for c in creator_list:
        creators.add(c)

    return creators


def generate_all_documentation(directory, output_dir):
    # Get all the patterns from the provided directory
    patterns = glob.glob("**/*.owl", recursive=True, root_dir=directory)
    patterns += glob.glob("**/*.ttl", recursive=True, root_dir=directory)

    # Nuke the previous contents of the file
    with open(f"{output_dir}/patterns.tex", "w") as output:
        output.write("\\chapter{Patterns}\n")
        output.write("\\label{sec:mods}\n")
        output.write("%"*35+"\n")
        output.write(
            "We list the individual modules of the ontology, together with their axioms and explanations thereof. Each axiom is listed only once (for now), i.e. some axioms pertaining to a module may be found in the axiom set listed for an earlier listed module. Schema diagrams are provided throughout, but the reader should keep in mind that while schema diagrams are very useful for understanding an ontology \\cite{odp-documentation}, they are also inherently ambiguous.")
        output.write("\n\n")
    # Hardcoded info for now
    acknowledgement = "This work was supported by The National Science Foundation through the Award \\#2033521."
    section_order = ["overview", "cqs", "usecases", "formalization", "submodules", "views", "entanglements", "examples"]
    # Generate sections for the patterns and get contributors
    contributors = set()
    for pattern in patterns:
        # Useful print out just in case something goes wrong
        print(f"Generating {pattern}")
        pattern_file = os.path.join(directory, pattern)
        pattern_contributors = generate_pattern_documentation(section_order, pattern_file, output_dir)
        contributors.update(pattern_contributors)
    # Regenerate the preamble
    generate_preamble(contributors, acknowledgement, output_dir)


if __name__ == "__main__":
    argParser = argparse.ArgumentParser(
        prog="Takes the turtle owl files and create documentation in LaTeX",
    )

    argParser.add_argument(
        "input",
        nargs="*",
        default="../patterns",
        help="Input directory"
    )

    argParser.add_argument(
        "output",
        nargs="*",
        default="../documentation",
        help="Output directory"
    )

    args = argParser.parse_args()

    input_dir = args.input[0] if type(args.input) is list else args.input
    output_dir = args.output[0] if type(args.output) is list else args.output

    input_dir = "./"
    output_dir = "/home/bddave/Desktop/modular-ontology-design-library/documentation"

    generate_all_documentation(input_dir, output_dir)
