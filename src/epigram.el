(setq load-path (append (list ".") load-path))

(load "emacs-epigram-interpreted.el")

(setq epigram-executable (concat default-directory "Epigram-bin"))

(install-epigram)
(switch-to-buffer epigram-buffer)
(switch-to-buffer-other-window horace-buffer)
