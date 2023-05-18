;;; cctt.el --- Mode for the cctt programming language -*- lexical-binding: t -*-
;; URL: https://github.com/AndrasKovacs/cctt
;; Package-version: 1.0
;; Package-Requires: ((emacs "24.1") (cl-lib "0.5"))
;; Keywords: languages

;;; Commentary:
;; This package provides a major mode for editing proofs or programs
;; in cctt, an implementation of a cartesian cubical type theory.

(require 'comint)
(require 'cl-lib)

;;;; Customization options

(defgroup cctt nil "Options for cctt-mode"
  :group 'languages
  :prefix 'cctt-
  :tag "cctt")

;;;; Syntax

(defvar cctt-keywords
  '("inductive" "higher" "import" "let" "module")
  "Keywords.")

(defvar cctt-operations
  '("Glue" "glue" "unglue" "hcom" "com" "coe" "refl" "U" "I" "ap" "case")
  "Operations.")

(defvar cctt-special
  '("undefined")
  "Special operators.")

(defvar cctt-keywords-regexp
  (regexp-opt cctt-keywords 'words)
  "Regexp that recognizes keywords.")

(defvar cctt-operations-regexp
  (regexp-opt cctt-operations 'words)
  "Regexp that recognizes operations.")

(defvar cctt-operators-regexp
  (regexp-opt '(":" "->" "→" "∙" "=" ":=" "|" "\\" "λ" "*" "×" "_" "@" "." "⁻¹" "[" "]") t)
  "Regexp that recognizes operators.")

(defvar cctt-special-regexp
  (regexp-opt cctt-special 'words)
  "Regexp that recognizes special operators.")

(defvar cctt-def-regexp "^[[:word:]'-]+"
  "Regexp that recognizes the beginning of a definition.")

(defvar cctt-font-lock-keywords
  `((,cctt-keywords-regexp . font-lock-keyword-face)
    (,cctt-operations-regexp . font-lock-builtin-face)
    (,cctt-operators-regexp . font-lock-variable-name-face)
    (,cctt-special-regexp . font-lock-warning-face)
    (,cctt-def-regexp . font-lock-function-name-face))
  "Font-lock information, assigning each class of keyword a face.")

(defvar cctt-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\{  "(}1nb" st)
    (modify-syntax-entry ?\}  "){4nb" st)
    (modify-syntax-entry ?-  "_ 123" st)
    (modify-syntax-entry ?\n ">" st)
    (modify-syntax-entry ?\\ "." st)
    st)
  "Syntax table with Haskell-style comments.")


;;;###autoload
(define-derived-mode cctt-mode prog-mode
  "cctt"
  "Major mode for editing cctt files."

  :syntax-table cctt-syntax-table

  ;; Make comment-dwim do the right thing for Cubical
  (set (make-local-variable 'comment-start) "--")
  (set (make-local-variable 'comment-end) "")

  ;; Code for syntax highlighting
  (setq font-lock-defaults '(cctt-font-lock-keywords))

  ;; Clear memory
  (setq cctt-keywords-regexp nil)
  (setq cctt-operators-regexp nil)
  (setq cctt-special-regexp nil))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.cctt\\'" . cctt-mode))

(provide 'cctt)
