# Chapter 8: Practical Examples

## Backup Scripts
Automate the process of backing up files and directories.

Example:
```bash
#!/bin/bash
src="/path/to/source"
dest="/path/to/destination"
tar -czf $dest/backup_$(date +%Y%m%d).tar.gz $src
```

## Automation Scripts
Automate repetitive tasks to save time and effort.

Example:
```bash
#!/bin/bash
for file in *.txt; do
  mv "$file" "${file%.txt}.bak"
done
```

## Parsing Logs
Extract useful information from log files.

Example:
```bash
#!/bin/bash
logfile="/var/log/syslog"
grep "error" $logfile
```

## System Monitoring Scripts
Monitor system resources and send alerts if necessary.

Example:
```bash
#!/bin/bash
threshold=80
usage=$(df / | grep / | awk '{ print $5 }' | sed 's/%//')
if [ $usage -gt $threshold ]; then
  echo "Disk usage is above $threshold%"
fi
```

## Conclusion
In this chapter, we covered practical examples of Bash scripts, including backup scripts, automation scripts, parsing logs, and system monitoring scripts. In the next chapter, we will explore best practices for writing Bash scripts.
