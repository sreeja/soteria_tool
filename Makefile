pull update:
	# svn update
	git pull

push commit:
	# svn commit -m ''
	git add -u
	git commit --allow-empty-message -m ""
	git push origin master
