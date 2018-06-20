---
title:  Logical Foundations in Idris
author:
 - Benjamin C. Pierce et al.
 - Eric Bailey et al.
language: en

documentclass: amsbook
classoption: twoside
papersize: b5
geometry: margin=1in

toc: true
toc-depth: 1

header-includes:
 - \IfFontExistsTF{Montserrat Regular}{
     \setmainfont{Montserrat Regular}
   }{}

 - \IfFontExistsTF{Fira Sans Regular}{
     \setsansfont{Fira Sans Regular}
   }{}

 - \IfFontExistsTF{Fira Code Retina}{
     \setmonofont[
       Contextuals={Alternate}
     ]{Fira Code Retina}[
       Scale=0.75
     ]
   }{}

---

  <!--- Extra Definitions -->

\long\def\ignore#1{}

\newcommand{\nil}{\ \texttt{[]}\ }
\newcommand{\app}{\ \texttt{++}\ }
