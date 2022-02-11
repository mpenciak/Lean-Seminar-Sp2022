# Lean-Seminar-Sp2022

Storing all of the content from the Learning Lean Seminar from Spring 2022

## Downloading the repo

If you have the whole Lean toolchain up and running <https://leanprover-community.github.io/get_started.html> then the best way of getting everything off this repo is by running

```[bash]
leanproject get https://github.com/mpenciak/Lean-Seminar-Sp2022.git
```

If you don't have it all working, then simply running

```[bash]
git pull https://github.com/mpenciak/Lean-Seminar-Sp2022.git
```

will do the trick, but none of the demos will work because the dependencies will be unable to resolve. Eventually once you get Lean up and running on your personal computer you'll have to run

```[bash]
leanproject pull
```

to get all of the mathlib files.

If none of this makes sense yet, that's ok! We'll talk about it soon in the seminar soon!
