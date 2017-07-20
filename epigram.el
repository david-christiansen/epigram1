(setq epigram-root (getenv "EPIGRAM_ROOT"))
(setq load-path (append (list (concat epigram-root "/src")) load-path))
(load "emacs-epigram-interpreted.el")

;; emacs is flexible about dir separators in windows, but can't figure 
;; out the .exe part which windows has to have
(setq epigram-executable 
	(concat epigram-root "/src/Epigram-bin" (getenv "EPIGRAM_EXT")))

(install-epigram)
(switch-to-buffer epigram-buffer)
(switch-to-buffer-other-window horace-buffer)
