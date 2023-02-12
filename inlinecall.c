#include <sys/queue.h>

#include <dwarf.h>
#include <err.h>
#include <fcntl.h>
#include <libdwarf.h>
#include <libelf.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

enum {
	F_SUBPROGRAM,
	F_INLINE_COPY,
};

TAILQ_HEAD(, die_info) diehead = TAILQ_HEAD_INITIALIZER(diehead);

struct die_info {
	Dwarf_Off		*addr_lo;
	Dwarf_Off		*addr_hi;
	int			naddrs;
	Dwarf_Unsigned		line;
	const char		*file;
	int			flag;
	TAILQ_ENTRY(die_info)	next;
};

static char **srcfiles;

static void *
emalloc(size_t nb)
{
	void *p;

	if ((p = malloc(nb)) == NULL)
		err(1, "malloc");
	return (p);
}

static void
parse_die(Dwarf_Debug dbg, Dwarf_Die die, void *data, int level, int flag)
{
	static Dwarf_Die die_root;
	Dwarf_Die die_next;
	Dwarf_Ranges *ranges, *rp;
	Dwarf_Attribute attp, *attr_list;
	Dwarf_Off dieoff, cuoff, culen, v_off;
	Dwarf_Addr v_addr;
	Dwarf_Addr *addr_lo, *addr_hi;
	Dwarf_Unsigned v_udata, line, nbytes;
	Dwarf_Signed nattr, v_sdata, nranges;
	Dwarf_Half tag, attr, form;
	Dwarf_Bool v_flag;
	Dwarf_Error error;
	struct die_info *di;
	const char *str;
	char *file = NULL;
	char *v_str;
	int naddrs;
	int res, i, found = 0;

	/* Save the root DIE so that we can re-parse it. */
	if (level == 0)
		die_root = die;

	if (dwarf_dieoffset(die, &dieoff, &error) != DW_DLV_OK) {
		warnx("%s", dwarf_errmsg(error));
		goto cont;
	}
	if (dwarf_die_CU_offset_range(die, &cuoff, &culen, &error) != DW_DLV_OK) {
		warnx("%s", dwarf_errmsg(error));
		cuoff = 0;
	}
	if (dwarf_tag(die, &tag, &error) != DW_DLV_OK) {
		warnx("%s", dwarf_errmsg(error));
		goto cont;
	}
	if (tag != DW_TAG_subprogram && tag != DW_TAG_inlined_subroutine)
		goto cont;
	if (flag == F_SUBPROGRAM && tag == DW_TAG_subprogram) {
		if (dwarf_hasattr(die, DW_AT_inline, &v_flag, &error) !=
		    DW_DLV_OK) {
			warnx("%s", dwarf_errmsg(error));
			goto cont;
		}
		if (!v_flag)
			goto cont;
		res = dwarf_attr(die, DW_AT_name, &attp, &error);
		if (res != DW_DLV_OK) {
			if (res == DW_DLV_ERROR)
				warnx("%s", dwarf_errmsg(error));
			goto cont;
		}
		if (dwarf_formstring(attp, &v_str, &error) != DW_DLV_OK) {
			warnx("%s", dwarf_errmsg(error));
			goto cont;
		}
		if (strcmp(v_str, (char *)data) != 0)
			goto cont;
		found = 1;
	} else if (flag == F_INLINE_COPY) {
		/*
		 * XXX I'm not checking against DW_TAG_inlined_subroutine since
		 * since I'm not sure whether we can have DW_TAG_subprogram
		 * also work as an inline copy. An example of this is <0x1004>.
		 */
		res = dwarf_attr(die, DW_AT_abstract_origin, &attp, &error);
		if (res != DW_DLV_OK) {
			if (res == DW_DLV_ERROR)
				warnx("%s", dwarf_errmsg(error));
			goto cont;
		}
		if (dwarf_formref(attp, &v_off, &error) != DW_DLV_OK) {
			warnx("%s", dwarf_errmsg(error));
			goto cont;
		}
		v_off += cuoff;
		if (v_off != (Dwarf_Off)data)
			goto cont;
		if (dwarf_hasattr(die, DW_AT_ranges, &v_flag, &error) !=
		    DW_DLV_OK) {
			warnx("%s", dwarf_errmsg(error));
			goto cont;
		}
		if (v_flag) {
			/* DIE has ranges */
			res = dwarf_attr(die, DW_AT_ranges, &attp, &error);
			if (res != DW_DLV_OK) {
				if (res == DW_DLV_ERROR)
					warnx("%s", dwarf_errmsg(error));
				goto cont;
			}
			if (dwarf_global_formref(attp, &v_off, &error) !=
			    DW_DLV_OK) {
				warnx("%s", dwarf_errmsg(error));
				goto cont;
			}
			if (dwarf_get_ranges(dbg, v_off, &ranges, &nranges,
			    &nbytes, &error) != DW_DLV_OK) {
				warnx("%s", dwarf_errmsg(error));
				goto cont;
			}
			naddrs = nranges - 1;
			addr_lo = emalloc(naddrs * sizeof(Dwarf_Off));
			addr_hi = emalloc(naddrs * sizeof(Dwarf_Off));
			for (i = 0; i < naddrs; i++) {
				rp = &ranges[i];
				res = dwarf_attr(die_root, DW_AT_low_pc, &attp,
				    &error);
				if (res != DW_DLV_OK) {
					if (res == DW_DLV_ERROR)
						warnx("%s", dwarf_errmsg(error));
					break;
				}
				if (dwarf_formaddr(attp, &v_addr, &error) !=
				    DW_DLV_OK) {
					warnx("%s", dwarf_errmsg(error));
					break;
				}
				addr_lo[i] = v_addr + rp->dwr_addr1;
				addr_hi[i] = v_addr + rp->dwr_addr2;
			}
			dwarf_ranges_dealloc(dbg, ranges, nranges);
		} else {
			/* DIE has high/low PC boundaries */
			res = dwarf_attr(die, DW_AT_low_pc, &attp, &error);
			if (res != DW_DLV_OK) {
				if (res == DW_DLV_ERROR)
					warnx("%s", dwarf_errmsg(error));
				goto cont;
			}
			if (dwarf_formaddr(attp, &v_addr, &error) != DW_DLV_OK) {
				warnx("%s", dwarf_errmsg(error));
				goto cont;
			}
			res = dwarf_attr(die, DW_AT_high_pc, &attp, &error);
			if (res != DW_DLV_OK) {
				if (res == DW_DLV_ERROR)
					warnx("%s", dwarf_errmsg(error));
				goto cont;
			}
			if (dwarf_formudata(attp, &v_udata, &error) !=
			    DW_DLV_OK) {
				warnx("%s", dwarf_errmsg(error));
				goto cont;
			}
			naddrs = 1;
			addr_lo = emalloc(sizeof(Dwarf_Off));
			addr_hi = emalloc(sizeof(Dwarf_Off));
			addr_lo[0] = v_addr;
			addr_hi[0] = v_addr + v_udata;
		}
	} else
		goto cont;

	/* Get file:line */
	attr = (flag == F_SUBPROGRAM) ? DW_AT_decl_file : DW_AT_call_file;
	res = dwarf_attr(die, attr, &attp, &error);
	if (res != DW_DLV_OK) {
		if (res == DW_DLV_ERROR)
			warnx("%s", dwarf_errmsg(error));
		goto skip;
	}
	if (dwarf_formudata(attp, &v_udata, &error) != DW_DLV_OK) {
		warnx("%s", dwarf_errmsg(error));
		goto cont;
	}
	file = srcfiles[v_udata - 1];

	attr = (flag == F_SUBPROGRAM) ? DW_AT_decl_line: DW_AT_call_line;
	res = dwarf_attr(die, attr, &attp, &error);
	if (res != DW_DLV_OK) {
		if (res == DW_DLV_ERROR)
			warnx("%s", dwarf_errmsg(error));
		goto skip;
	}
	if (dwarf_formudata(attp, &line, &error) != DW_DLV_OK) {
		warnx("%s", dwarf_errmsg(error));
		goto cont;
	}
skip:
	di = emalloc(sizeof(struct die_info));
	di->flag = flag;
	if (file != NULL) {
		di->file = file;
		di->line = line;
	} else
		di->file = NULL;
	if (di->flag == F_INLINE_COPY) {
		di->naddrs = naddrs;
		di->addr_lo = addr_lo;
		di->addr_hi = addr_hi;
	}
	TAILQ_INSERT_TAIL(&diehead, di, next);
cont:
	/*
	 * Inline copies might appear before the declaration, so we need to
	 * re-parse the CU.
	 *
	 * The rationale for choosing to re-parse the CU instead of using a
	 * hash table of DIEs is that, because we re-parse only when an inline
	 * definition of the function we want is found. This means that,
	 * statistically, we won't have to re-parse many times at all
	 * considering that only a handful of CUs will define the function,
	 * whereas if we have used a hash table, we would first need to parse
	 * the whole CU at once and store all DW_TAG_inlined_subroutine DIEs
	 * (so that we can match them afterwards). In this case, we always have
	 * to "parse" twice -- first the CU, then the DIE table -- and also,
	 * the program would use much more memory since we would have allocated
	 * DIEs, which most of them would never be used.
	 */
	if (found) {
		die = die_root;
		data = (void *)dieoff;
		level = 0;
		flag = F_INLINE_COPY;
	}

	res = dwarf_child(die, &die_next, &error);
	if (res == DW_DLV_ERROR)
		warnx("%s", dwarf_errmsg(error));
	else if (res == DW_DLV_OK)
		parse_die(dbg, die_next, data, level + 1, flag);

	res = dwarf_siblingof(dbg, die, &die_next, &error);
	if (res == DW_DLV_ERROR)
		warnx("%s", dwarf_errmsg(error));
	else if (res == DW_DLV_OK)
		parse_die(dbg, die_next, data, level, flag);

	/*
	 * Deallocating on level 0 will attempt to double-free, since die_root
	 * points to the first DIE. We'll deallocate the root DIE in main().
	 */
	if (level > 0)
		dwarf_dealloc(dbg, die, DW_DLA_DIE);
}

static void
print_info(void)
{
	struct die_info *di;
	int i;

	/* Clean up as well */
	while (!TAILQ_EMPTY(&diehead)) {
		di = TAILQ_FIRST(&diehead);
		TAILQ_REMOVE(&diehead, di, next);
		if (di->flag == F_INLINE_COPY) {
			for (i = 0; i < di->naddrs; i++) {
				printf("\t[0x%jx - 0x%jx]",
				    di->addr_lo[i],
				    di->addr_hi[i]);
				if (di->file != NULL) {
					printf("\t%s:%lu\n",
					    di->file, di->line);
				} else
					putchar('\n');
			}
			free(di->addr_lo);
			free(di->addr_hi);
		} else if (di->flag == F_SUBPROGRAM) {
			printf("%s:%lu\n", di->file, di->line);
		}
		free(di);
	}
}

int
main(int argc, char *argv[])
{
	Elf *elf;
	Dwarf_Debug dbg;
	Dwarf_Die die;
	Dwarf_Signed nfiles;
	Dwarf_Error error;
	char *func, *file;
	int fd;
	int res = DW_DLV_OK;

	if (argc < 3) {
		fprintf(stderr, "usage: %s function debug_file\n", *argv);
		return (1);
	}
	func = argv[1];
	file = argv[2];

	if (elf_version(EV_CURRENT) == EV_NONE)
		errx(1, "elf_version(): %s", elf_errmsg(-1));
	if ((fd = open(file, O_RDONLY)) < 0)
		err(1, "open(%s)", file);
	if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
		errx(1, "elf_begin(): %s", elf_errmsg(-1));
	if (elf_kind(elf) == ELF_K_NONE)
		errx(1, "not an ELF file: %s", file);
	if (dwarf_elf_init(elf, DW_DLC_READ, NULL, NULL, &dbg, &error) !=
	    DW_DLV_OK)
		errx(1, "dwarf_elf_init(): %s", dwarf_errmsg(error));

	do {
		while ((res = dwarf_next_cu_header(dbg, NULL, NULL, NULL, NULL,
		    NULL, &error)) == DW_DLV_OK) {
			die = NULL;
			TAILQ_INIT(&diehead);
			while (dwarf_siblingof(dbg, die, &die, &error) ==
			    DW_DLV_OK) {
				srcfiles = NULL;
				if (dwarf_srcfiles(die, &srcfiles, &nfiles,
				    &error) != DW_DLV_OK)
					warnx("%s", dwarf_errmsg(error));
				parse_die(dbg, die, func, 0, F_SUBPROGRAM);
			}
			dwarf_dealloc(dbg, die, DW_DLA_DIE);
			print_info();
		}
		if (res == DW_DLV_ERROR)
			warnx("%s", dwarf_errmsg(error));
	} while (dwarf_next_types_section(dbg, &error) == DW_DLV_OK);

	dwarf_finish(dbg, &error);
	elf_end(elf);
	close(fd);

	return (0);
}
