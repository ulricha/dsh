  WITH
    posts_and_quotes AS (
      SELECT "spiegelPostUrl",
             max("spiegelPostThreadUrl") AS "spiegelPostThreadUrl",
             (CASE WHEN (count("spiegelQuotePostUrl") > 0) THEN 1.0 ELSE 0.0 END) AS bq
      FROM "spiegelPosts"
      LEFT OUTER JOIN "spiegelQuotes" ON "spiegelPostUrl" = "spiegelQuotePostUrl"
      GROUP BY "spiegelPostUrl"
    ),
    
    threads_and_posts AS (
    SELECT sum (bq) / count ("spiegelPostUrl") AS "interactivity", max("spiegelThreadRating") AS "rating"
      FROM "spiegelThreads", "posts_and_quotes"
      WHERE "spiegelThreadUrl" = "spiegelPostThreadUrl" AND "spiegelThreadRating" > 0
      GROUP BY "spiegelThreadUrl"
      ORDER BY "interactivity"
    )
  
    SELECT * FROM threads_and_posts;