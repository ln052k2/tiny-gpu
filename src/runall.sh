
#!/bin/bash
rsync -avh --delete ~/Projects/tiny-gpu kayhyn@mo.ece.pdx.edu:tgpu
#ssh kayhyn@mo.ece.pdx.edu -t "zsh -l -c 'cd tgpu/tiny-gpu && rm -rf work && vlog -lint -source -file sources.f && zsh -i'"
ssh kayhyn@mo.ece.pdx.edu -t "zsh -l -c 'cd tgpu/tiny-gpu && make && zsh -i'"
