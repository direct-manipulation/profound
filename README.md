# Profound 0.3 Alpha

[Profound][phome] is an experiment in formula linking as an interaction method.

> Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>  
> Copyright 2013  INRIA  

See the file LICENSE for licensing details

## 0. Download

Profound can be downloaded from GitHub:

    $ git clone https://github.com/chaudhuri/profound.git

## 1. Prerequisites

You will need:

* [OCaml] version 3.12.1 or later
* [ocaml-findlib][findlib]
* [OCaml Batteries Included][batteries]
* [LablGTK2][lablgtk]
* [Menhir]
* A LaTeX distribution (eg. TeXLive) that contains AMS Math and dvipng

Please consider using [OPAM] to install OCaml and the above libraries.
Latest version of everything preferred.

This will probably only work on a Linux system.

## 2. Building

There is nothing to configure.

Just run "make".

It will produce the binary ./profound.native


## 3. Invoking

Use the --help option for a quick overview of all options.

### 3.1. Theorem in the command line

    $  ./profound.native  "a | ~a"

### 3.2. Theorems read from a file

    $  echo "a | ~a" > a.p
    $  ./profound.native -i a.p


## 4. User Interface

Profound has a very minimalistic user interface.

The main theorem is displayed centered in the window.

The only other widget is a small status bar that sometimes displays
hints or error messages.

### 4.1. Navigation

The user can navigate to a suitable subformula of the theorem.
Navigation in the subformula tree is done with the cursor keys. The
current selected subformula is indicated in braces {}.

To start navigating, you will have to descend at least once (with the
down key).

Hit Shift-up to stop navigating subformulas, _i.e._, to go all the way
back to the top.

### 4.2. Linking

The primary operation that the user is expected to perform is
_linking_.

To initiate a link (technical term: mark a source), press the `Return`
or `Enter` keys. This will turn the current selection blue. Any
subformula of the theorem can be a source -- not just the atoms.

To complete a link (technical term: mark a sink), navigate to another
subformula that is ancestrally joined to the source via a par or a ?.
Then hit `Return` or `Enter` again. Any suitable subformula can be a
sink, not just atoms.

When a link completes, the source and sink interact hereditarily, with
all ties broken in favor of the sink having outermost scope.
Intuitively, the source is "brought to" the sink.

### 4.3. History

The proof state is presented as a linear _timeline_ with the _present_
shown in the middle in a large font, and the _past_ and _future_ below
and above the present.

Whenever a link is resolved or the current theorem is rewritten, the
previous state of the theorem is prepended to the _past_.

To go back to an earlier form, hit `Ctrl-Z`.

Going back in history shows the known future _above_ the theorem line.
You can return to any of the futures in the current timeline by
hitting `Ctrl-Y`.

Note that any rule application that modifies the text of the theorem
will alter the current timeline and therefore will remove the futures
from the earlier timeline. (There is currently no way to restore a lost
timeline -- after a number of experiments, I came to the conclusion
that allowing too much branching in time adds only confusion.)

By default only the three most recent past and future states are
shown. You can change this with the `-hist-lines` command line
parameter, and dynamically using the `+` and `-` keys.

### 4.4. Saving and quitting

To quit, hit `Ctrl-Q`.

If the input came from a file, the current state of the proof is saved
on quitting. When working on the same file again, the previous state is
restored, including the full undo and redo histories.

A save can also be forced at any time using `Ctrl-S`.

### 4.5. Other interactions

On any subformula

- `Delete` rewrites it to 0. Note that `0 \plus A` and `A \plus 0`
  will be rewritten to `A` eagerly when ascending out of the current
  context.

If the current subformula is a ?-formula and has no marks in any subformula, then:

- `Shift-Return` / `Shift-Enter` contracts it, _i.e._, it rewrites ?A to ?A
  \par ?A.

- `Shift-Delete` applies weakening to it, _i.e._, it rewrites ?A to \bot.

- `?` applies dereliction to it, _i.e._, it rewrites ?A to A.

If the current subformula is an existential, then:

- `Shift-Return` opens a dialog box asking for a witness to substitute
  for the variable. Witnesses are allowed to use any of the variables
  in scope of the existential -- these will be captured. All free
  identifiers in the witness terms are assumed to be signature
  constants, and are displayed in a different (sans-serif) font.

[phome]: http://chaudhuri.info/software/profound/
[OCaml]: http://caml.inria.fr/ocaml
[findlib]: http://projects.camlcity.org/projects/findlib.html
[batteries]: http://batteries.forge.ocamlcore.org/
[lablgtk]: http://lablgtk.forge.ocamlcore.org/
[OPAM]: http://opam.ocamlpro.com/
[Menhir]: http://gallium.inria.fr/~fpottier/menhir/
