test_that("Task constructs objects correctly", {
  name = "task 1"
  t <- task(name)

  expect_equal(t@name, name)
})
