import Project.qtCatalan

open DyckWord

/-- Basic Dyck word `( )`. -/
def example₁ : DyckWord := (0 : DyckWord).nest

/-- Concatenate two copies of `example₁`, giving the word `()()`. -/
def example₂ : DyckWord := example₁ + example₁

/-- Nest `example₂` for a slightly longer example `(()())`. -/
def example₃ : DyckWord := example₂.nest

#eval areaWord example₁
#eval areaWord example₂
#eval areaWord example₃

#eval area example₁
#eval area example₂
#eval area example₃

#eval dinv example₁
#eval dinv example₂
#eval dinv example₃

#eval bounce example₁
#eval bounce example₂
#eval bounce example₃

#eval qtCatalan 0 ℕ 1 1
#eval qtCatalan 1 ℕ 1 1
#eval qtCatalan 2 ℕ 1 1

#eval qtCatalanAlt 0 ℕ 1 1
#eval qtCatalanAlt 1 ℕ 1 1
#eval qtCatalanAlt 2 ℕ 1 1
