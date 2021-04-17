module Main where
import ABox
import Algorithms
main :: IO ()
main = do
  let student = Primitive "Student"
  let graduate = Primitive "Graduate"
  let graduateStudent = And student graduate
  let notGS = Not graduateStudent
  print notGS
