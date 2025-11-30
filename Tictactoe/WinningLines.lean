import Tictactoe.Rules

namespace Tictactoe

/-- All coordinates in a given row. -/
def row (i : Fin 3) : Finset Coord :=
  Finset.univ.image (fun j => (i, j))

/-- All coordinates in a given column. -/
def col (j : Fin 3) : Finset Coord :=
  Finset.univ.image (fun i => (i, j))

/-- Main and anti-diagonal coordinates. -/
def mainDiag : Finset Coord :=
  Finset.univ.image (fun i => (i, i))

def antiDiag : Finset Coord :=
  Finset.univ.image (fun i => (i, Fin.rev i))

def rows : Finset (Finset Coord) :=
  Finset.univ.image row

def cols : Finset (Finset Coord) :=
  Finset.univ.image col

def diagonals : Finset (Finset Coord) :=
  ([mainDiag, antiDiag] : List (Finset Coord)).toFinset

def rowList : List (Finset Coord) := (List.finRange 3).map row
def colList : List (Finset Coord) := (List.finRange 3).map col
def diagList : List (Finset Coord) := [mainDiag, antiDiag]
def winningLinesList : List (Finset Coord) := rowList ++ colList ++ diagList

/-- The eight winning lines: three rows, three columns, two diagonals. -/
def winningLines : Finset (Finset Coord) :=
  winningLinesList.toFinset

/-- Player `p` wins on board `b` if some winning line is filled with `p`. -/
def wins (p : Player) (b : Board) : Prop :=
  ∃ line ∈ winningLines, ∀ pos ∈ line, b pos.1 pos.2 = some p

instance (p : Player) (b : Board) : Decidable (wins p b) :=
  decidable_of_decidable_of_iff (by unfold wins; exact Iff.rfl)

/-- If every main-diagonal cell is marked by `p`, then `p` wins. -/
lemma wins_mainDiag {b : Board} {p : Player}
    (h : ∀ i, b i i = some p) : wins p b := by
  classical
  refine ⟨mainDiag, ?_, ?_⟩
  · simp [winningLines, winningLinesList, diagList]
  · intro pos hpos
    rcases Finset.mem_image.mp hpos with ⟨i, _, rfl⟩
    simp [h]

lemma row_nonempty (i : Fin 3) : (row i).Nonempty := by
  classical
  refine ⟨(i, ⟨0, by decide⟩), ?_⟩
  simp [row]

lemma col_nonempty (j : Fin 3) : (col j).Nonempty := by
  classical
  refine ⟨(⟨0, by decide⟩, j), ?_⟩
  simp [col]

lemma mainDiag_nonempty : mainDiag.Nonempty := by
  classical
  refine ⟨(⟨0, by decide⟩, ⟨0, by decide⟩), ?_⟩
  simp [mainDiag]

lemma antiDiag_nonempty : antiDiag.Nonempty := by
  classical
  refine ⟨(⟨0, by decide⟩, Fin.rev ⟨0, by decide⟩), ?_⟩
  simp [antiDiag]

lemma winningLines_nonempty {line : Finset Coord} (h : line ∈ winningLines) :
    line.Nonempty := by
  classical
  rw [winningLines, winningLinesList, List.toFinset_append, List.toFinset_append] at h
  rcases Finset.mem_union.mp h with hrc | hdiag
  · rcases Finset.mem_union.mp hrc with hrow | hcol
    · have : line ∈ rows := by
        simpa [rows, rowList] using hrow
      rcases Finset.mem_image.mp this with ⟨i, _, rfl⟩
      exact row_nonempty _
    · have : line ∈ cols := by
        simpa [cols, colList] using hcol
      rcases Finset.mem_image.mp this with ⟨j, _, rfl⟩
      exact col_nonempty _
  · have : line ∈ diagonals := by
        simpa [diagonals, diagList] using hdiag
    have hdiag' : line = mainDiag ∨ line = antiDiag := by
      simpa [diagonals] using this
    rcases hdiag' with rfl | rfl
    · exact mainDiag_nonempty
    · exact antiDiag_nonempty

end Tictactoe
