cd analysis/
lake exe cache get
lake -R -Kenv=dev build Analysis:docs
lake build
cd ../book/
lake exe analysis-book
cd ../