test_that("Experiment constructs objects correctly", {
  name = "Experiment 1"
  print(typeof(name))
  exp <- Experiment(name)

  expect_equal(exp@name, name)
  expect_vector(exp@tasks)
  expect_length(exp@tasks, 0)
  expect_vector(exp@conditions)
  expect_length(exp@conditions, 0)
  expect_vector(exp@trials)
  expect_length(exp@trials, 0)
})
