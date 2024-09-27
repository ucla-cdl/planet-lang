test_that("Condition constructs objects correctly", {
  name = "condition 1"
  c <- condition(name)

  expect_equal(c@name, name)
})
