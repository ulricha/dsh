--
-- PostgreSQL database dump
--

SET statement_timeout = 0;
SET client_encoding = 'UTF8';
SET standard_conforming_strings = off;
SET check_function_bodies = false;
SET client_min_messages = warning;
SET escape_string_warning = off;

SET search_path = public, pg_catalog;

SET default_tablespace = '';

SET default_with_oids = false;

--
-- Name: Facilities; Type: TABLE; Schema: public; Owner: postgres; Tablespace: 
--

CREATE TABLE "Facilities" (
    facility text NOT NULL,
    categorie text NOT NULL
);


ALTER TABLE public."Facilities" OWNER TO postgres;

--
-- Name: Features; Type: TABLE; Schema: public; Owner: postgres; Tablespace: 
--

CREATE TABLE "Features" (
    facility text NOT NULL,
    feature text NOT NULL
);


ALTER TABLE public."Features" OWNER TO postgres;

--
-- Name: Meanings; Type: TABLE; Schema: public; Owner: postgres; Tablespace: 
--

CREATE TABLE "Meanings" (
    feature text NOT NULL,
    meaning text NOT NULL
);


ALTER TABLE public."Meanings" OWNER TO postgres;

--
-- Data for Name: Facilities; Type: TABLE DATA; Schema: public; Owner: postgres
--

COPY "Facilities" (facility, categorie) FROM stdin;
SQL	QLA
ODBC	API
LINQ	LIN
Links	LIN
Rails	ORM
Ferry	LIB
Kleisli	QLA
ADO.NET	ORM
HaskellDB	LIB
\.


--
-- Data for Name: Features; Type: TABLE DATA; Schema: public; Owner: postgres
--

COPY "Features" (facility, feature) FROM stdin;
Kleisli	nest
Kleisli	comp
Kleisli	type
Links	comp
Links	type
Links	SQL
LINQ	nest
LINQ	comp
LINQ	type
HaskellDB	comp
HaskellDB	type
HaskellDB	SQL
SQL	aval
SQL	type
SQL	SQL
Rails	nest
Rails	maps
ADO.NET	maps
ADO.NET	comp
ADO.NET	type
Ferry	list
Ferry	nest
Ferry	comp
Ferry	aval
Ferry	type
Ferry	SQL
\.


--
-- Data for Name: Meanings; Type: TABLE DATA; Schema: public; Owner: postgres
--

COPY "Meanings" (feature, meaning) FROM stdin;
maps	admits user-defined object mappings
list	respects list order
nest	supports data nesting
comp	has compositional syntax and semantics
aval	avoids query avalanches
type	is statically type-checked
SQL	guarantees translation to SQL
\.


--
-- Name: Facilities_pkey; Type: CONSTRAINT; Schema: public; Owner: postgres; Tablespace: 
--

ALTER TABLE ONLY "Facilities"
    ADD CONSTRAINT "Facilities_pkey" PRIMARY KEY (facility);


--
-- Name: Features_pkey; Type: CONSTRAINT; Schema: public; Owner: postgres; Tablespace: 
--

ALTER TABLE ONLY "Features"
    ADD CONSTRAINT "Features_pkey" PRIMARY KEY (facility, feature);


--
-- Name: Meanings_pkey; Type: CONSTRAINT; Schema: public; Owner: postgres; Tablespace: 
--

ALTER TABLE ONLY "Meanings"
    ADD CONSTRAINT "Meanings_pkey" PRIMARY KEY (feature);


--
-- Name: foreign facility; Type: FK CONSTRAINT; Schema: public; Owner: postgres
--

ALTER TABLE ONLY "Features"
    ADD CONSTRAINT "foreign facility" FOREIGN KEY (facility) REFERENCES "Facilities"(facility);


--
-- Name: foreign feature; Type: FK CONSTRAINT; Schema: public; Owner: postgres
--

ALTER TABLE ONLY "Features"
    ADD CONSTRAINT "foreign feature" FOREIGN KEY (feature) REFERENCES "Meanings"(feature);


--
-- Name: public; Type: ACL; Schema: -; Owner: postgres
--

REVOKE ALL ON SCHEMA public FROM PUBLIC;
REVOKE ALL ON SCHEMA public FROM postgres;
GRANT ALL ON SCHEMA public TO postgres;
GRANT ALL ON SCHEMA public TO PUBLIC;


--
-- PostgreSQL database dump complete
--

