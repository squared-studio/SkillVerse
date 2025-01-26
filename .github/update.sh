#!/bin/bash

rm -r *.md

echo "# VLSI Training" > README.md

LIST=$(find -mindepth 1 -maxdepth 1 -type d ! -name ".*" | sed "s/.*\///g")
for i in ${LIST} ; do
    echo "  - ## [$(echo ${i} | sed -e 's/_/ /g' -e 's/\b\(.\)/\u\1/g')](${i}.md)" >> README.md
    echo "# $(echo ${i} | sed -e 's/_/ /g' -e 's/\b\(.\)/\u\1/g')" > ${i}.md
    LIST2=$(find ${i} -mindepth 1 -maxdepth 1 -type f -name "chapter_*.md")
    for j in ${LIST2} ; do
        TITLE=$(cat ${j} | grep "^# " | sed "s/^# //g")
        echo "## $(echo "${j}" | sed "s/.*chapter_0*//g" | sed "s/\..*//g"). [$(echo ${TITLE} | sed -e 's/_/ /g' -e 's/\b\(.\)/\u\1/g')](${j})" >> ${i}.md
        cat ${j} | grep "^## " | sed "s/^## /  - /g" >> ${i}.md
    done
    echo "" >> ${i}.md
done

echo "" >> README.md
