#!/bin/sh
# Select the step-index type of the Iris build.
#
#   scripts/stepindex.sh nat        SI := Nat (as upstream Iris-Lean)
#   scripts/stepindex.sh ordinal    SI := Ordinals.Ordinal.{3}
#   scripts/stepindex.sh check      print the active choice; fail if the active files are not
#                                   equal to a stored choice (CI runs this)
#
# A choice is a directory Iris/StepIndexChoices/<name>/ with two files. The script copies them:
#
#   StepIndexChoice.lean      ->  Iris/Iris/Algebra/StepIndexChoice.lean
#   StepIndexChoiceTest.lean  ->  Iris/IrisTest/StepIndexChoice.lean
#
# After a change, run `lake build` in Iris/; Lake rebuilds the modules that use the index.
# To change a choice, edit its stored files and run the script again.

set -eu

root=$(cd "$(dirname "$0")/.." && pwd)
choices=$root/Iris/StepIndexChoices
lib=$root/Iris/Iris/Algebra/StepIndexChoice.lean
test=$root/Iris/IrisTest/StepIndexChoice.lean

usage() {
  echo "usage: scripts/stepindex.sh <choice> | check" >&2
  echo "choices: $(ls "$choices" | tr '\n' ' ')" >&2
}

# Print the name of the stored choice that is equal to the active files.
active() {
  for d in "$choices"/*/; do
    if cmp -s "$d/StepIndexChoice.lean" "$lib" && cmp -s "$d/StepIndexChoiceTest.lean" "$test"
    then
      basename "$d"
      return 0
    fi
  done
  return 1
}

case "${1:-}" in
  check)
    if name=$(active); then
      echo "Active step-index choice: $name"
    else
      echo "error: $lib or $test is not equal to a stored choice in $choices." >&2
      echo "Put the change in the stored choice, then run scripts/stepindex.sh <choice>." >&2
      exit 1
    fi
    ;;
  "" | -h | --help)
    usage
    exit 1
    ;;
  *)
    if [ ! -d "$choices/$1" ]; then
      echo "error: unknown choice '$1'." >&2
      usage
      exit 1
    fi
    if ! active > /dev/null; then
      echo "error: the active choice files have changes that are not in a stored choice." >&2
      echo "Put the changes in $choices/<choice>/ first, so that they are not lost." >&2
      exit 1
    fi
    cp "$choices/$1/StepIndexChoice.lean" "$lib"
    cp "$choices/$1/StepIndexChoiceTest.lean" "$test"
    echo "Step-index choice: $1. Now run 'lake build' in Iris/."
    ;;
esac
