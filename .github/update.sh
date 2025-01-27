#!/bin/bash

rm -r *.md

echo "# VLSI Training" > README.md

LIST=$(find -mindepth 1 -maxdepth 1 -type d ! -name ".*" | sed "s/.*\///g")
for i in ${LIST} ; do
    echo "  - ## [$(echo ${i} | sed -e 's/_/ /g' -e 's/\b\(.\)/\u\1/g')](${i}.md)" >> README.md
    echo "# $(echo ${i} | sed -e 's/_/ /g' -e 's/\b\(.\)/\u\1/g')" > ${i}.md
    LIST1=$(find ${i} -mindepth 1 -maxdepth 1 -type f -name "chapter_*.md")
    for j in ${LIST1} ; do
        TMP_NAME=$(echo ${j} | sed "s/chapter_/temp_chapter_/g")
        mv ${j} ${TMP_NAME}
    done
    count=1
    LIST2=$(find ${i} -mindepth 1 -maxdepth 1 -type f -name "temp_chapter_*.md")
        for j in ${LIST2} ; do
            FINAL_NAME=$(echo ${j} | sed "s/temp_chapter_.*\./chapter_$(printf "%03d." ${count})/g")
            mv ${j} ${FINAL_NAME}
            count=$((count + 1))
        done
    LIST3=$(find ${i} -mindepth 1 -maxdepth 1 -type f -name "chapter_*.md")
    for j in ${LIST3} ; do
        TITLE=$(cat ${j} | grep -m 1 "^# " | sed "s/^# //g")
        echo "## $(echo "${j}" | sed "s/.*chapter_0*//g" | sed "s/\..*//g"). [$(echo ${TITLE} | sed -e 's/_/ /g' -e 's/\b\(.\)/\u\1/g')](${j})" >> ${i}.md
        cat ${j} | grep "^## " | sed "s/^## /  - /g" >> ${i}.md
    done
    echo "" >> ${i}.md
done

echo "" >> README.md
