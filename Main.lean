import Examples

open Examples

def parseNumbers (contents : String) : List Nat :=
  contents.splitOn "\n"
    |>.filter (· != "")
    |>.filterMap (·.trimAscii.toString.toNat?)


def main (args : List String) : IO Unit := do
  let [sortAlg, inputFile] := args
    | IO.eprintln "Usage: examples <sort-alg: ins | bst><input> <output>" *> IO.Process.exit 1
  let contents ← IO.FS.readFile inputFile
  let numbers := parseNumbers contents
  let outputFile := inputFile ++ ".sorted"

  match sortAlg with
  | "ins" => do
    let sorted := insertion_sort numbers
    let outputStr := String.intercalate "\n" (sorted.map toString)
    IO.FS.writeFile outputFile outputStr
    IO.println s!"Sorted {numbers.length} numbers using insertion sort and wrote to {outputFile}"
  | "bst" => do
    let sorted := bst_sort numbers
    let outputStr := String.intercalate "\n" (sorted.map toString)
    IO.FS.writeFile outputFile outputStr
    IO.println s!"Sorted {numbers.length} numbers using BST sort and wrote to {outputFile}"
  | _ => do
    IO.eprintln "Unknown sorting algorithm. Use 'ins' for insertion sort or 'bst" *> IO.Process.exit 1
