(TeX-add-style-hook
 "main"
 (lambda ()
   (setq TeX-command-extra-options
         "-shell-escape")
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("babel" "english")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "inputenc"
    "babel"
    "listings"
    "bytefield"
    "xcolor"
    "tikz"
    "pgf-umlsd"
    "afterpage"
    "hyperref")
   (LaTeX-add-environments
    '("returnanother" LaTeX-env-args ["argument"] 4)
    '("returnanother" LaTeX-env-args ["argument"] 5)
    '("returnanother" LaTeX-env-args ["argument"] 6)))
 :latex)

